﻿# This code is major rewrite/extension of disassembler.py from this repository
# https://github.com/marian-m12l/s9ke-toolchain
# this is not a generic disassembler, it's more a reverser's helper tool to quickly understand code/memory layout
#
# features on top of standard disassembler:
# - map file describing memory layout, which parts are data and which code
# - support for symbols, aiming for faster orientation
# - added displaying of IMM8 and IMM16 as ascii, when reasonable in order to understand possible magic values
# - conversion of some common instruction patterns to the simpler form (ie. reg.l=0xXX, reg.h=0xYY is converted to reg=0xYYXX)
# 
# Original license:
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

# 1.0.0 jindroush 30.06.2025 initial published version
# 1.0.1 jindroush 03.07.2025 added 'pointer' keyword, changed all hex prints to lowercase, added 'wbstr' keyword
# 1.0.2 jindroush 05.07.2025 added second pass for autosymbol creation
# 1.1.0 jindroush 10.07.2025 added smarter instruction mutator, added mapping of output-to-file, instruction mutator now one pass,
#                                instruction disassembler now does not modify input word list
#
# known bugs/todos:
# - empty lines between blocks are not printed in the correct way
# - still thinking about showing labels more visibly
# - unify comments to use either ; or # and put it on the same column(?)
#

import os
import sys
import hashlib
import re

from collections import defaultdict
from datetime import datetime

# === Keywords ===
KEYWORDS = {
    'infile',		#defines input filename
    'outfile',		#defines output filename
    'output',		#defines binding between output facility and output handle
    'org',		#changes origin of code
    'wstr',		#real unicode string (question is if such are used at all in the firmware)
    'wbstr',		#byte-in-word string, using GBK chinese encoding
    'str',		#byte ascii string
    'skip',		#skips N byte area
    'word',		#prints Nx words
    'dword',		#prints Nx dwords
    'asm',		#prints disassembly of N bytes
    'jumptable',	#interprets Nx words as lo-words of 32bit address (hi-word is the hi-word of the address of the table)
    'pointer',		#32bit pointer to code
}

# === Globals ===

g_mapfile = None
g_handle_input = None

g_outfiles = dict()
g_output_handles = dict()
g_output2handle = dict()

parsed_lines = []
g_PC = 0
g_pointer = 0
g_previous_processed = None

g_symbolsName2Value = dict()
g_symbolsValue2Name = dict()
g_ext_comments = dict()

g_crossref = defaultdict(int)
g_instruction_store = []
g_last_function_start = None

g_auto_symbols = 1

g_calls = dict()

# === Helpers ===

def parse_int_or_hex(value, lineno):
    try:
        return int(value, 0)
    except ValueError:
        raise ValueError(f"[Line {lineno}] Invalid integer or hex value: '{value}'")

def parse_decimal_multiply(value, lineno):
    if value.endswith('x') and value[:-1].isdigit():
        return int(value[:-1])
    raise ValueError(f"[Line {lineno}] Expected decimal-multiply format like '123x', got '{value}'")

def parse_line(line, lineno):
    #fixme duplicated code, pfui!
    if re.match(r'^\t0x[0-9a-fA-F]+\t.+$', line):
        parts = line.split('\t')
        if len(parts) != 3:
            raise ValueError(f"[Line {lineno}] Expected exactly two tabs: '{line}'")

        _, hex_part, text_part = parts
        if not hex_part.lower().startswith("0x"):
            raise ValueError(f"[Line {lineno}] Hex part must start with 0x: '{hex_part}'")

        try:
            addr = int(hex_part, 16)
        except ValueError:
            raise ValueError(f"[Line {lineno}] Invalid hex value: '{hex_part}'")

        if not text_part.strip():
            raise ValueError(f"[Line {lineno}] Comment text is empty")

        add_ext_comment(text_part.strip(), addr)
        return


    # Separate the main part (keyword, param1) and optional tab-separated fields
    if '\t' in line:
        main_part, tab_part = line.split('\t', 1)
    else:
        main_part, tab_part = line, None

    parts = main_part.strip().split()
    if not parts:
        return None

    keyword = parts[0]
    if keyword not in KEYWORDS:
        raise ValueError(f"[Line {lineno}] Unknown keyword: '{keyword}'")

    if len(parts) < 2:
        raise ValueError(f"[Line {lineno}] Missing parameter for keyword '{keyword}'")

    param1 = parts[1]

    param2_dict = {}
    if tab_part:
        for item in tab_part.split('\t'):
            if ':' not in item:
                raise ValueError(f"[Line {lineno}] Invalid key:value pair in optional tab data: '{item}'")
            key, val = item.split(':', 1)  # split only on first colon
            key = key.strip()
            if key == 'symbol':
                key = 'sym' 
            param2_dict[key] = val.strip()  # allow spaces in value

    return (keyword, param1, param2_dict, lineno, line)

# === Pointer logic ===

def pointer_move(length):
    global g_PC, g_pointer
    if length % 2 != 0:
        raise Exception(f"pointer_move: length {length} must be even")
    g_pointer += length
    g_PC += length // 2

def print_line_header( r_PC=None, pointer=None ):
    global g_PC, g_pointer
    if r_PC is None: r_PC = g_PC 
    if pointer is None: pointer = g_pointer

    DIS.write(f"[{pointer:06x}] 0x{r_PC:06x} ")

def empty_line( type ):
    global g_previous_processed
    if type != g_previous_processed:
        DIS.write(f'\n')

def add_auto_symbol( prefix, value ):
    global g_symbolsValue2Name, g_symbolsName2Value

    if g_auto_symbols:
        symbol = f"auto_{prefix}_{value:06x}"
        if value not in g_symbolsValue2Name:
            g_symbolsValue2Name[value] = symbol
            if symbol not in g_symbolsName2Value:
                g_symbolsName2Value[symbol] = value

def add_symbol( name, value ):
    global g_symbolsName2Value
    global g_symbolsValue2Name
    if name in g_symbolsName2Value:
        raise Exception( f"duplicate definition of symbol {name}" )
    if value in g_symbolsValue2Name:
        if g_symbolsValue2Name[value].startswith('auto'):
            del g_symbolsName2Value[g_symbolsValue2Name[value]]
            
        else:
            raise Exception( f"duplicate definition of value {value:06x}/symbol {name}" )
    g_symbolsName2Value[name] = value
    g_symbolsValue2Name[value] = name

def add_ext_comment( name, value ):
    global g_ext_comments
    if value in g_ext_comments:
        raise Exception( f"duplicate definition of comment 0x{value:06x}/{name}" )
    g_ext_comments[value] = name

def escape_unicode_string(s):
    result = []
    for ch in s:
        code = ord(ch)
        if ch == '\\':
            result.append('\\\\')
        elif code == 0:
            result.append("\\0")
        elif code == 0xa:
            result.append("\\n")
        elif (
            0x20 <= code <= 0x7E or        # Printable ASCII
            0x00A0 <= code <= 0x00FF or    # Latin-1 Supplement
            0x0100 <= code <= 0x024F or    # Latin Extended-A and B
            0x1E00 <= code <= 0x1EFF       # Latin Extended Additional
            or 0x4E00 <= code <= 0x9FFF #chinese basic
        ):
            result.append(ch)
        elif code < 0x20 or code == 0x7F:
            result.append(f"\\x{code:02X}")
        else:
            result.append(f"\\u{code:04X}")
    return ''.join(result)

# === Pre-parse functions ===

def infile_preparse(param1, param2_dict, lineno):
    global g_handle_input
    if not os.path.isfile(param1):
        raise Exception(f"[Line {lineno}] File '{param1}' does not exist.")

    g_handle_input = open(param1, 'rb')
    return {'filename': param1, 'consumed_bytes': 0 }

def outfile_preparse( param1, param2_dict, lineno ):
    global g_outfiles, g_output_handles

    if 'filename' in param2_dict:
        fn = param2_dict['filename']
        g_outfiles[param1] = fn
        g_output_handles[param1] = None
        del param2_dict['filename']
    else:
        raise Exception( f"outfile_preparse: expected 'filename' in '{param2_dict}'" )

    return {'consumed_bytes': 0 }

def output_preparse( param1, param2_dict, lineno ):
    global g_out

    if 'handle' in param2_dict:
        handle = param2_dict['handle']
        g_output2handle[param1] = handle
        del param2_dict['handle']
    else:
        raise Exception

    return {'consumed_bytes': 0 }

def org_preparse(param1, param2_dict, lineno):
    num = parse_int_or_hex(param1, lineno)
    global g_PC
    g_PC = num
    return {'address': num, 'consumed_bytes': 0 }

def wstr_preparse(param1, param2_dict, lineno):
    num = parse_int_or_hex(param1, lineno)
    ldict = {'length': num, 'consumed_bytes': num }

    if 'comment' in param2_dict:
        ldict['comment'] = param2_dict['comment']
        del param2_dict['comment']

    g_handle_input.seek( num, 1 )
    return ldict

def wbstr_preparse(param1, param2_dict, lineno):
    num = parse_int_or_hex(param1, lineno)
    ldict = {'length': num, 'consumed_bytes': num }

    if 'comment' in param2_dict:
        ldict['comment'] = param2_dict['comment']
        del param2_dict['comment']

    g_handle_input.seek( num, 1 )
    return ldict

def str_preparse(param1, param2_dict, lineno):
    num = parse_int_or_hex(param1, lineno)

    ldict = {'length': num, 'consumed_bytes': num }

    if 'comment' in param2_dict:
        ldict['comment'] = param2_dict['comment']
        del param2_dict['comment']

    g_handle_input.seek( num, 1 )
    return ldict

def skip_preparse(param1, param2_dict, lineno):
    num = parse_int_or_hex(param1, lineno)
    g_handle_input.seek( num, 1 )
    return {'length': num, 'consumed_bytes': num }

def word_preparse(param1, param2_dict, lineno):
    num = parse_decimal_multiply(param1, lineno)
    ldict = {'count': num, 'consumed_bytes': num * 2 }

    if 'comment' in param2_dict:
        ldict['comment'] = param2_dict['comment']
        del param2_dict['comment']

    g_handle_input.seek( num * 2, 1 )
    return ldict

def dword_preparse(param1, param2_dict, lineno):
    num = parse_decimal_multiply(param1, lineno)
    ldict = {'count': num, 'consumed_bytes': num * 4 }

    if 'comment' in param2_dict:
        ldict['comment'] = param2_dict['comment']
        del param2_dict['comment']

    g_handle_input.seek( num*4, 1 )
    return ldict

def pointer_preparse(param1, param2_dict, lineno):
    num = parse_decimal_multiply(param1, lineno)
    ldict = {'count': num, 'consumed_bytes': num * 4 }

    if 'comment' in param2_dict:
        ldict['comment'] = param2_dict['comment']
        del param2_dict['comment']

    g_handle_input.seek( num*4, 1 )
    return ldict

def asm_preparse(param1, param2_dict, lineno):
    length = parse_int_or_hex(param1, lineno)

    if length % 2 != 0:
        raise Exception("asm_execute: length must be even")

    data = g_handle_input.read(length)
    if len(data) != length:
        raise Exception("asm_execute: not enough data")

    words = []
    for i in range(0, length, 2):
        word = int.from_bytes(data[i:i+2], 'little')
        words.append(word)

    word1 = words.pop(0)
    word2 = None

    while word1 is not None:
        high = word1 >> 8;
        low = word1 & 0xFF;

        # Call
        if high & 0b_1000_0000 == 0:
            #abs_addr = ((high & 0b_0111_1111) << 8) + low
            pass
        # Jump
        elif ((high >> 4) & 0b_0000_1111) == 0b_1000:
            offset = signed12( ((high & 0b_0000_1111) << 8) + low ) # Offset is signed !
            add_auto_symbol( "jmp_dst", g_PC+1+offset )
        # Jump Condition
        elif ((high >> 4) & 0b_0000_1111) == 0b_1001:
            cond = high & 0b_0000_1111
            offset = signed8(low)   # Offset is signed !
            add_auto_symbol( f"cond_j{(condsuffix(cond))}_dst", g_PC+1+offset )
        # Callff (2-words instruction)
        elif high == 0b_1111_1101:
            abs_addr_high = low
            word2 = words.pop(0)
            abs_addr_low = word2
            abs_addr = (abs_addr_high << 16) | abs_addr_low
            add_auto_symbol( "callff_dst", abs_addr )
            if abs_addr not in g_calls:
                g_calls[abs_addr] = dict()
                g_calls[abs_addr]['from'] = []
            g_calls[ abs_addr ]['from'].append(g_PC)
        # Jumpff (2-words instruction)
        elif high == 0b_1111_1110:
            abs_addr_high = low
            word2 = words.pop(0)
            abs_addr_low = word2
            abs_addr = (abs_addr_high << 16) | abs_addr_low
            add_auto_symbol( "jmpff_dst", abs_addr )
        else:
            pass

        pointer_move(2)
        if word2 is not None:
           pointer_move(2)

        if not words:
            word1 = None
        else:
            word1 = words.pop(0)
        word2 = None
    #loop ends

    return {'length': length, 'consumed_bytes': 0 }

def jumptable_preparse(param1, param2_dict, lineno):
    global g_PC
    num = parse_decimal_multiply(param1, lineno)

    add_auto_symbol( "jmptbl", g_PC )

    for _ in range(num):
        data = g_handle_input.read(2)
        if len(data) != 2:
            raise Exception("jumptable_execute: not enough data")
        value = int.from_bytes(data, 'little')
        value = value | ( g_PC & 0x00FF0000 )

        add_auto_symbol( "jmptbl_dst", value )
        pointer_move(2)

    #g_handle_input.seek( num * 2, 1 )
    return {'count': num, 'consumed_bytes': 0 }

# === Execute functions ===

def infile_execute(params):
    global g_handle_input, g_output_handles, g_PC, g_pointer, g_mapfile, g_outfiles

    input_file = params['filename']

    for id,fname in g_outfiles.items():
        handle = open( fname, "w", encoding="utf-8")
        g_output_handles[id] = handle

    for id,handle in g_output2handle.items():
        if handle in g_output_handles:
            #this creates uppercased symbol which in fact means handle
            globals()[id.upper()] = g_output_handles[handle]
        else:
            raise Exception

    print( f"processing {input_file}..." )
    print( f"...to these files: {(', '.join(g_outfiles.values()))}" )
    # MD5 hash
    with open(input_file, 'rb') as f:
        md5 = hashlib.md5(f.read()).hexdigest()
    DIS.write(f"#processing input file '{input_file}' with md5 {md5}\n")
    g_handle_input.seek(0)

    # File modification date
    stat = os.stat(g_mapfile)
    dt = datetime.fromtimestamp(stat.st_mtime)
    formatted = dt.strftime("%-d.%-m.%Y %H:%M:%S") if os.name != 'nt' else dt.strftime("%#d.%#m.%Y %H:%M:%S")
    DIS.write(f"#using map file '{g_mapfile}', last modified: {formatted}\n")

    # --- MD5 and modified date of this script ---
    this_path = os.path.abspath(__file__)
    with open(this_path, 'rb') as f:
        script_md5 = hashlib.md5(f.read()).hexdigest()
    script_stat = os.stat(this_path)
    dt_script = datetime.fromtimestamp(script_stat.st_mtime)
    formatted_script = dt_script.strftime("%-d.%-m.%Y %H:%M:%S") if os.name != 'nt' else dt_script.strftime("%#d.%#m.%Y %H:%M:%S")
    script_file = os.path.basename( this_path)
 
    DIS.write(f"#generated by script '{script_file}', md5: {script_md5}, last modified: {formatted_script}\n")

    g_PC = 0
    g_pointer = 0

def outfile_execute(params):
    pass

def output_execute(params):
    pass

def org_execute(params):
    global g_PC
    g_PC = params['address']

def wstr_execute(params):
    length = params['length']
    data = g_handle_input.read(length)
    if len(data) != length:
        raise Exception(f"wstr_execute: expected {length} bytes, got {len(data)}")
    try:
        raw_text = data.decode('utf-16-le')
    except UnicodeDecodeError:
        raw_text = "<invalid UTF-16>"
    empty_line( "wstr" )
    print_line_header()
    text = escape_unicode_string( raw_text )
    DIS.write(f'.wstr "{text}"')
    if 'comment' in params:
        DIS.write( f"  #{(params['comment'])}" )
        del params['comment']
    DIS.write("\n")

    pointer_move(length)

def wbstr_execute(params):
    length = params['length']
    data = g_handle_input.read(length)
    if len(data) != length:
        raise Exception(f"wbstr_execute: expected {length} bytes, got {len(data)}")

    # Check that every second byte is 0x00 (odd indices)
    for i in range(1, len(data), 2):
        if data[i] != 0x00:
            raise ValueError(f"Invalid padding byte at index {i}: expected 0x00, found 0x{byte_data[i]:02X}")

    # Extract every low byte (even indices)
    raw_bytes = data[::2]

    # Decode as GBK
    text = raw_bytes.decode('gbk')
    empty_line( "wbstr" )
    print_line_header()
    text = escape_unicode_string( text )
    DIS.write(f'.wbstr "{text}"')
    if 'comment' in params:
        DIS.write( f"  #{(params['comment'])}" )
        del params['comment']
    DIS.write("\n")

    pointer_move(length)

def str_execute(params):
    length = params['length']
    data = g_handle_input.read(length)
    if len(data) != length:
        raise Exception(f"str_execute: expected {length} bytes, got {len(data)}")
    try:
        raw_text = data.decode('ascii')
    except UnicodeDecodeError:
        raw_text = "<invalid ASCII>"
    empty_line( "str" )
    print_line_header()
    text = escape_unicode_string( raw_text )
    DIS.write(f'.str "{text}"')
    if 'comment' in params:
        DIS.write( f"  #{(params['comment'])}" )
        del params['comment']
    DIS.write("\n")

    pointer_move(length)

def word_execute(params):
    empty_line( "word" )
    count = params['count']

    comment = None

    for _ in range(count):
        data = g_handle_input.read(2)
        if len(data) != 2:
            raise Exception("word_execute: not enough data")
        value = int.from_bytes(data, 'little')
        print_line_header()
        DIS.write(f".word 0x{value:04x}")

        if 'comment' in params:
            comment = params['comment']
            del params['comment']

        if comment is None and g_PC in g_ext_comments:
            comment = g_ext_comments[g_PC]

        if comment is not None:
            DIS.write( f"  #{comment}" )
            comment = None
        DIS.write("\n")
        pointer_move(2)

def dword_execute(params):
    empty_line( "dword" )
    count = params['count']
    for _ in range(count):
        data = g_handle_input.read(4)
        if len(data) != 4:
            raise Exception("dword_execute: not enough data")
        value = int.from_bytes(data, 'little')
        print_line_header()
        DIS.write(f".dword 0x{value:08x}")
        if 'comment' in params:
            DIS.write( f"  #{(params['comment'])}" )
            del params['comment']
        DIS.write("\n")
        pointer_move(4)

def pointer_execute(params):
    empty_line( "pointer" )
    count = params['count']
    for _ in range(count):
        data = g_handle_input.read(4)
        if len(data) != 4:
            raise Exception("pointer_execute: not enough data")
        value = int.from_bytes(data, 'little')
        print_line_header()

        if value in g_symbolsValue2Name:
            DIS.write( f".pointer {(g_symbolsValue2Name[value])} ;(0x{value:06x})" )
        else:
            DIS.write( f".pointer 0x{value:06x}")

        if 'comment' in params:
            DIS.write( f"  #{(params['comment'])}" )
            del params['comment']
        DIS.write("\n")
        pointer_move(4)

def skip_execute(params):
    empty_line( "skip" )
    length = params['length']
    print_line_header()
    skipped = g_handle_input.read(length)
    if len(skipped) != length:
        raise Exception("skip_execute: not enough data")

    if all(b in (0x00, 0xFF) for b in skipped):
        desc = f".skip {length} bytes (0x00 or 0xFF only)"
    else:
        desc = f".skip {length} bytes (mixed data)"

    DIS.write(desc + "\n")
    pointer_move(length)

def asm_execute(params):
    empty_line( "asm" )
    length = params['length']

    if length % 2 != 0:
        raise Exception("asm_execute: length must be even")

    data = g_handle_input.read(length)
    if len(data) != length:
        raise Exception("asm_execute: not enough data")

    words = []
    for i in range(0, length, 2):
        word = int.from_bytes(data[i:i+2], 'little')
        words.append(word)

    #clear previous block data
    reset_instructions()

    instructions_disassembly(words)
    instructions_mutator()
    instructions_printer()

    reset_instructions()

def jumptable_execute(params):
    global g_PC, g_crossref

    empty_line( "jumptable" )
    count = params['count']

    for _ in range(count):
        data = g_handle_input.read(2)
        if len(data) != 2:
            raise Exception("jumptable_execute: not enough data")
        #to make sense of it
        #PCH (top 8 bits of 24bit address) is not changed
        #so it's extracted from current instruction pointer
        #that means that jumptable should not cross 'segment' boundary
        value = int.from_bytes(data, 'little')
        value = value | ( g_PC & 0x00FF0000 )
        print_line_header()

        DIS.write( f"{(data[0]):02x} {(data[1]):02x}" + ( " " * 16 ) )
        if value in g_symbolsValue2Name:
            DIS.write( f".jumptable {(g_symbolsValue2Name[value])} ;(0x{value:06x})\n" )
        else:
            DIS.write(f".jumptable 0x{value:06x}\n")
        g_crossref[value] += 1
        pointer_move(2)


def find_addr_in_routine(addr):
    for start, info in g_calls.items():
        end = info.get('epilogue_address', -1)
        if start <= addr <= end:
            delta = addr - start
            sym = f"0x{start:06x}"
            if start in g_symbolsValue2Name:
                sym = g_symbolsValue2Name[start]
            return f"{sym}+0x{delta:x}"
            
    return ""

def dump_symbols_table():
    SYMBOLS.write( "SYMBOL TABLE:\n" )
    for value, key in sorted((v, k) for k, v in g_symbolsName2Value.items()):
        SYMBOLS.write(f"0x{value:06x}  {key}\n")

def dump_cross_table():
    CROSS.write( "CROSSREF TABLE:\n" )
    for key, value in sorted((k,v) for k,v in g_crossref.items()):
        CROSS.write(f"0x{key:06x} {value:4d}" )
        if key in g_symbolsValue2Name:
            CROSS.write( f"\t{(g_symbolsValue2Name[key])}" )
        CROSS.write("\n")

def dump_calls_table():
    CALLS.write( "CALLS TABLE:\n" )
    for r_PC, d_onecall in sorted(g_calls.items()):
        CALLS.write( f"0x{r_PC:06x}" )
        if 'name' in d_onecall:
            CALLS.write( f" '{(d_onecall['name'])}'" )
        else:
            if r_PC in g_symbolsValue2Name:
                CALLS.write( f" '{g_symbolsValue2Name[r_PC]}'" )
        CALLS.write("\n")
        if 'prologue_type' in d_onecall:
            CALLS.write( f"  Prologue: {(d_onecall['prologue_type'])}\n" )
        if 'prologue_pars' in d_onecall and d_onecall['prologue_pars'] is not None:
            CALLS.write( f"  Prologue parameters: {(d_onecall['prologue_pars'])}\n" )
        if 'prologue_locals' in d_onecall and d_onecall['prologue_locals'] is not None:
            CALLS.write( f"  Prologue locals: {(d_onecall['prologue_locals'])}\n" )

        if 'epilogue_type' in d_onecall:
            CALLS.write( f"  Epilogue: {(d_onecall['epilogue_type'])}\n" )

        if 'epilogue_address' in d_onecall:
            eadr = d_onecall[ 'epilogue_address' ]
            CALLS.write( f"  Epilogue addr: 0x{eadr:06x}\n" )
            flen = eadr - r_PC
            CALLS.write( f"  Length: 0x{flen:x}\n" )
        #CALLS.write( f"{(d_onecall)}\n" )

        for addr in sorted( d_onecall['from'] ):
            res = find_addr_in_routine(addr)
            CALLS.write( f"    0x{addr:06x} {res}\n" )
        CALLS.write( "\n" )

# === Main ===

BLOCK_NONE = 1
BLOCK_MAPPING = 2
BLOCK_SYMBOLS = 3

def mapfile_parse(filename):
    errors = []
    global parsed_lines, g_previous_processed, g_mapfile, g_PC, g_pointer

    g_mapfile = filename


    #PREPARE pass
    current_block = BLOCK_NONE
    with open(filename, encoding="utf-8") as f:
        for lineno, line in enumerate(f, start=1):

            if '#' in line:
                line = line.split('#', 1)[0]
            line = line.rstrip()
            if not line:
                continue

            if current_block == BLOCK_NONE:
                if line == '[MAPPING]':
                    current_block = BLOCK_MAPPING
                    continue
                raise Exception( f"unexpected line encountered {lineno}:{line}" )

            if current_block == BLOCK_MAPPING:
                try:
                    if line == '[SYMBOLS]':
                        current_block = BLOCK_SYMBOLS
                        continue

                    parsed = parse_line(line, lineno)
                    if parsed:
                        keyword, param1, param2_dict, _, original = parsed
                        preparse = globals().get(f"{keyword}_preparse")
                        if not preparse:
                            raise Exception(f"[Line {lineno}] No preparse function for '{keyword}'")

                        if 'sym' in param2_dict:
                            add_symbol( param2_dict['sym'], g_PC )
                            del param2_dict['sym']
                        
                        param_dict = preparse(param1, param2_dict, lineno)
                        parsed_lines.append((keyword, param_dict, lineno, original))

                        pointer_move( param_dict[ 'consumed_bytes' ] )

                        if param2_dict:
                            raise Exception( f"Not all param2 were processed for {line}" )
                except Exception as e:
                    raise
                    #errors.append(str(e))

            elif current_block == BLOCK_SYMBOLS:

                if re.match(r'^0x[0-9a-fA-F]+\t.+$', line):
                    parts = line.rstrip('\n').split('\t')
                    if len(parts) != 2:
                        raise ValueError(f"[Line {lineno}] Expected exactly one tab: '{line}'")

                    hex_part, text_part = parts
                    if not hex_part.lower().startswith("0x"):
                        raise ValueError(f"[Line {lineno}] Hex part must start with 0x: '{hex_part}'")

                    try:
                        addr = int(hex_part, 16)
                    except ValueError:
                        raise ValueError(f"[Line {lineno}] Invalid hex value: '{hex_part}'")

                    if not text_part.strip():
                        raise ValueError(f"[Line {lineno}] Text part is empty")

                    add_symbol( text_part, addr )

                elif re.match(r'^\t0x[0-9a-fA-F]+\t.+$', line):
                    parts = line.split('\t')
                    if len(parts) != 3:
                        raise ValueError(f"[Line {lineno}] Expected exactly two tabs: '{line}'")

                    _, hex_part, text_part = parts
                    if not hex_part.lower().startswith("0x"):
                        raise ValueError(f"[Line {lineno}] Hex part must start with 0x: '{hex_part}'")

                    try:
                        addr = int(hex_part, 16)
                    except ValueError:
                        raise ValueError(f"[Line {lineno}] Invalid hex value: '{hex_part}'")

                    if not text_part.strip():
                        raise ValueError(f"[Line {lineno}] Comment text is empty")

                    add_ext_comment(text_part.strip(), addr)

                else:
                    raise ValueError(f"[Line {lineno}] Invalid format (expected: hex<TAB>string): '{line}'")
            else:
                raise Exception( "unknown block type" )

    #else:
    #    raise ValueError(f"[Line {lineno}] Invalid format: '{line}'")

    if errors:
        print("Errors during pre-parsing:")
        for err in errors:
            print(err)
        sys.exit(1)

    #EXECUTE pass
    g_handle_input.seek(0)
    g_PC = 0
    g_pointer = 0
    for keyword, param_dict, lineno, original in parsed_lines:
        execute = globals().get(f"{keyword}_execute")
        if execute:
            if keyword != 'asm':
                #todo first prints symbols then empty line, ugly, fixit
                if g_PC in g_symbolsValue2Name:
                    DIS.write( f"{(g_symbolsValue2Name[g_PC])}:\n" )
            execute(param_dict)
            if g_handle_input.tell() != g_pointer:
                cur = g_handle_input.tell()
                raise Exception( f"file pointer mismatch! {cur:08X} vs {g_pointer:08X}, last executed '{keyword}' with {param_dict}" )
            g_previous_processed = keyword
        else:
            print(f"[Line {lineno}] Warning: no execute function for '{keyword}'")

    print_line_header()
    DIS.write( "end of file processing!\n" )

    print( f"ended on {g_PC:06X}" )

    dump_symbols_table()
    dump_cross_table()
    dump_calls_table()


    print( "done!" )

# DISASM BEGIN
# large parts of this code are from marian, mostly the instruction joining and symbols are additions

def hex(val, digits):
    return "{0:#0{1}x}".format(val, digits+2)

def signed8(value):
    return -(value & 0x80) | (value & 0x7f)
def signed12(value):
    return -(value & 0x800) | (value & 0x7ff)
def signed16(value):
    return -(value & 0x8000) | (value & 0x7fff)

suffixes = ['eq', 'ne', 'gt', 'ge', 'lt', 'le', 'av', 'nav', 'ac', 'nac', 'mr0s', 'mr0ns', 'mv', 'nmv', 'ixv', 'irr']    # FIXME irr unsupported ???
def condsuffix(cond):
    return suffixes[cond]

registers_reg = ['X0', 'X1', 'R0', 'R1', 'Y0', 'Y1', 'MR0', 'MR1']
registers_reg1 = ['X0', 'X1', 'R0', 'R1', 'Y0', 'Y1', 'Ix0', 'Ix1']
registers_regL = ['X0', 'X1', 'R0', 'R1']
def register(reg):
    return registers_reg[reg]
def register1(reg):
    return registers_reg1[reg]
def registerL(reg):
    return registers_regL[reg]

hilo_suffixes = ['.h', '', '.l', '']     # FIXME index 0x01 unsupported ?!!
def hilo(L):
    return hilo_suffixes[L]

modifiers = ['', ', m', ', 1', ', -1']
def modifier(A):
    return modifiers[A]

operandXop = ['X0', 'X1', 'R0', 'R1']
def operand1(Xop):
    return operandXop[Xop]

operandYop = ['Y0', 'Y1', 'R0', 'R1']
def operand2(Yop):
    return operandYop[Yop]

lu2Mnemonics = ['BCLR', 'BSET', 'BTOG', 'BTST']
def lu2(LU2):
    return lu2Mnemonics[LU2]

indirectIxy = ['Ix0', 'Ix1', 'Iy0', 'Iy1']
def indirect(Ixy):
    return indirectIxy[Ixy]

shiftMnemonics = ['', 'SL', 'SRA', 'SRL']   # FIXME Shift Left Sign Extension ???
def shift(sf):
    return shiftMnemonics[sf]

destXY = ['X0', 'X1', 'Y0', 'Y1']
def dxy(DXY):
    return destXY[DXY]

pushpopMnemonics = ['Push', 'Pop']
def pushpop(pp):
    return pushpopMnemonics[pp]

ioRegisters = dict([
    (0x0000, 'SSF|System Status Flag Register'),
    (0x0001, 'SCR|System Control Register'),
    (0x0002, 'Ix0|Indirect Addressing Register x0' ),
    (0x0003, 'Ix1|Indirect Addressing Register x1' ),
    (0x0004, 'Im00'),
    (0x0005, 'Im01'),
    (0x0006, 'Im02'),
    (0x0007, 'Im03'),
    (0x0008, 'Im10'),
    (0x0009, 'Im11'),
    (0x000a, 'Im12'),
    (0x000b, 'Im13'),
    (0x000c, 'OPM_CTRL|Operation mode control'),
    (0x000d, 'RAMBk|RAM Bank selector for DM'),
    (0x000e, 'Ix0Bk|Ix0 Bank selector'),
    (0x000f, 'Ix1Bk|Ix1 Bank selector'),
    (0x0010, 'T0|Timer0'),
    (0x0011, 'T1|Timer1'),
    (0x0012, 'T2|Timer2'),
    (0x0013, 'Iy0|Indirect Addressing Register y0'),
    (0x0014, 'Iy1|Indirect Addressing Register y1'),
    (0x0015, 'PCH|Program counter high'),
    (0x0016, 'PCL|Program counter low'),
    (0x0017, 'MMR|MAC Mode register'),
    (0x0018, 'Sp|Stack Pointer'),
    (0x0019, 'MR2'),
    (0x001a, 'Iy0Bk|Iy0 Bank selector'),
    (0x001b, 'Iy1Bk|Iy1 Bank selector'),
    (0x001c, 'Iy0BkRAM'),
    (0x001d, 'Iy1BkRAM'),
    (0x001e, 'Ix2|Indirect Addressing Register x2'),
    (0x001f, 'Iy2|Indirect Addressing Register y2'),
    (0x0020, 'INTEN|Interrupt channel 1 Enable'),
    (0x0021, 'INTRQ|Interrupt channel 1 Request Flag'),
    (0x0022, 'INTPR|Interrupt channel 1 Priority'),
    (0x0023, 'INTCR|Interrupt channel 1 Clear Request'),
    (0x0024, 'PCR1|Peripheal control register 1'),
    (0x0025, 'OPM_CTRL1|Operation mode control 1'),
    (0x0026, 'ADC_FIFOSTATUS|ADC FIFO status register'),
    (0x0028, 'ADC_DATA|ADC result register'),
    (0x0029, 'WDT|Watch Dog Timer'),
    (0x002a, 'ADC_SET1|Control ADC signal 1'),
    (0x002b, 'ADC_SET2|Control ADC signal 2'),
    (0x002c, 'ImxL|Ix2 Modifier Register Linear mode'),
    (0x002d, 'ImxC|Ix2 Modifier Register Circular mode'),
    (0x002e, 'ImyL|Iy2 Modifier Register Linear mode'),
    (0x002f, 'ImyC|Iy2 Modifier Register Circular mode'),
    (0x0030, 'P0WKUPEN|P0 wake up enable register'),
    (0x0031, 'P1WKUPEN|P1 wake up enable register'),
    (0x0032, 'INTEN2|Interrupt Channel 2 Enable'),
    (0x0033, 'INTRQ2|Interrupt Channel 2 Request Flag'),
    (0x0034, 'INTPR2|Interrupt Channel 2 Priority'),
    (0x0035, 'INTCR2|Interrupt Channel 2 Clear Request'),
    (0x0036, 'IBx|Ix2 Base Address'),
    (0x0037, 'ILx|Ix2 Length'),
    (0x0038, 'IBy|Iy2 Base Address'),
    (0x0039, 'ILy|Iy2 Length'),
    (0x003a, 'IOSW|I/O Byte Swap Register'),
    (0x003b, 'SP1|Stack pointer 2 for OS'),
    (0x003c, 'IOSW2|I/O Byte Swap Register 2'),
    (0x003d, 'EVENT|Timer Event control register'),
    (0x003e, 'ShIdx|Shift amount of index shift'),
    (0x003f, 'ShV2|Shift result register'),
    (0x0040, 'T1CNTV|counter value of timer 1'),
    (0x0045, 'T0CNT|timer 0 counter register'),
    (0x0046, 'T1CNT|timer 1 counter register'),
    (0x0047, 'T0CNTV|counter value of timer 0'),
    (0x0048, 'INTEC|Interrupt Edge Control Register'),
    (0x0049, 'DAC_SET1|Control DAC signal 1'),
    (0x004a, 'DAC_SET2|Control DAC signal 2'),
    (0x004b, 'DAC_FIFOSTATUS|DAC FIFO status register'),
    (0x004c, 'T2CNT|Timer2 Counter Register'),
    (0x004d, 'EVENT0CNT|EVENT0 Count Value'),
    (0x004e, 'EVENT1CNT|EVENT1 Count Value'),
    (0x004f, 'EVENT2CNT|EVENT2 Count Value'),
    (0x0050, 'I2SCTRL|I2S Control Register'),
    (0x0051, 'PWM0|PWM control of P0.3'),
    (0x0052, 'PWM1|PWM control of P0.4'),
    (0x0053, 'PWM2|PWM control of P0.5'),
    (0x0054, 'PWM3|PWM control of P0.6'),
    (0x0055, 'DAOL|left channel DA output'),
    (0x0056, 'DAOR|right channel DA output'),
    (0x0057, 'SPIDATA0|SPI data buffer 0'),
    (0x0058, 'SPIDATA1|SPI data buffer 1'),
    (0x0059, 'SPIDATA2|SPI data buffer 2'),
    (0x005a, 'SPIDATA3|SPI data buffer 3'),
    (0x005b, 'SPIDATA4|SPI data buffer 4'),
    (0x005c, 'SPIDATA5|SPI data buffer 5'),
    (0x005d, 'SPICTRL|SPI Control Register'),
    (0x005e, 'SPICSC|SPI Chip Select Control'),
    (0x005f, 'SPITRANSFER|SPI Bit transfer Control'),
    (0x0061, 'SPIBR|SPI Baud rate register'),
    (0x0062, 'MSPSTAT|MSP Status Register'),
    (0x0063, 'MSPM1|MSP Mode Register 1'),
    (0x0064, 'MSPM2|MSP Mode Register 2'),
    (0x0065, 'MSPBUF|MSP Data Buffer Register'),
    (0x0066, 'MSPADR|MSP Address Register'),
    (0x0067, 'CHIP_ID'),

    (0x0068, 'P0En|I/O Port 0 Enable'),
    (0x0069, 'P0|I/O Port 0'),
    (0x006a, 'P0M|I/O Port 0 Direction'),
    (0x006b, 'P0PH|I/O Port 0 Pull High'),

    (0x006c, 'P1En|I/O Port 1 Enable'),
    (0x006d, 'P1|I/O Port 1'),
    (0x006e, 'P1M|I/O Port 1 Direction'),
    (0x006f, 'P1PH|I/O Port 1 Pull High'),

    (0x0070, '0x70' ),
    (0x0071, '0x71' ),
    (0x0072, '0x72' ),
    (0x0073, '0x73' ),

    (0x0074, 'P3En|I/O Port 3 Enable'),
    (0x0075, 'P3|I/O Port 3'),
    (0x0076, 'P3M|I/O Port 3 Direction'),
    (0x0077, 'P3PH|I/O Port 3 Pull High'),

    (0x0078, 'P4En|I/O Port 4 Enable'),
    (0x0079, 'P4|I/O Port 4'),
    (0x007a, 'P4M|I/O Port 4 Direction'),
    (0x007b, 'P4PH|I/O Port 4 Pull High'),

    (0x007c, 'SYSCONF|Internal system configuration'),
    (0x007d, 'ADP|SAR ADC input pin control'),
    (0x007e, 'ADM|SAR ADC mode control'),
    (0x007f, 'ADR|SAR ADC result')
])

def ioRegisterLabel(ioReg):
    return ioRegisters.get(ioReg, "NOT FOUND")

def reset_instructions():
    global g_instruction_store
    g_instruction_store = []

def store_instruction( word_array, mnemonic, parameters, comment ):
    global g_instruction_store

    rec = dict()
    rec['words'] = word_array
    rec['mnemonic'] = mnemonic
    rec['parameters'] = parameters
    rec['comment'] = comment

    rec['PC'] = g_PC
    rec['pointer'] = g_pointer
    g_instruction_store.append( rec )

#parameter format types
ADDR16 = 1
ADDR24 = 2
REG = 3
DM = 4
IMM8 = 5
RAM = 6
STR = 7
IO = 8
ROM = 9
IMM16 = 10

def format_param( param ):
    type = param[0]
    value = param[1]

    if type == REG:
        return value
    elif type == ADDR16:
        return "0x%04x" % value
    elif type == ADDR24:
        if value in g_symbolsValue2Name:
            return f"{(g_symbolsValue2Name[value])} (0x{value:06x})"
        return "0x%06x" % value
    elif type == STR:
        return value
    elif type == IO:
        return "IO[%s]" % value
    elif type == IMM8:
        return "0x%02x" % value
    elif type == IMM16:
        if value in g_symbolsValue2Name:
            return f"{(g_symbolsValue2Name[value])} (0x{value:04x})"
        return "0x%04x" % value
    elif type == RAM:
        return "RAM[%s]" % value
    elif type == ROM:
        return "ROM[%s]" % value
    elif type == DM:
        return "DM[0x%03x]" % value
    else:
        raise Exception( f"no formatting for type {type} of value {value}" )

def format_words_little_endian(words):
    lines = []
    for i in range(0, len(words), 3):
        chunk = words[i:i+3]
        # Format each word as "lo hi" in lowercase hex
        parts = [f"{w & 0xFF:02x} {w >> 8 & 0xFF:02x}" for w in chunk]
        line = ' '.join(parts)
        if len(chunk) == 3 and i + 3 < len(words):
            line += '+  '
        else:
            line = line.ljust(20)
        lines.append(line)
    return lines

#todo should we somehow format all comments in same column?
def print_stored_instruction( rec ):
    global g_crossref

    is_first_call_dest_instruction = False
    is_end_of_function = False

    r_PC = rec['PC']

    if r_PC in g_symbolsValue2Name:
        DIS.write( f"{(g_symbolsValue2Name[r_PC])}:\n" )
        if r_PC in g_calls:
            is_first_call_dest_instruction = True
            if 'name' not in g_calls[r_PC]:
                #print(f"{r_PC:06x} {(g_symbolsValue2Name[r_PC])}")
                g_calls[r_PC]['name'] = g_symbolsValue2Name[r_PC]

    print_line_header( r_PC, rec['pointer'])

    words = rec['words']
    formatted_bytes = format_words_little_endian( words )

    DIS.write( formatted_bytes.pop(0) )

    mnemonic = rec['mnemonic']
    params = []
    if rec['parameters']:
        params = rec['parameters'].copy()
    comment = rec['comment']

    if comment is None and r_PC in g_ext_comments:
       comment = g_ext_comments[r_PC]

    if mnemonic == '=':
        str = format_param( params.pop(0) )
        DIS.write( f" {str} = " )
        for param in params:
            str = format_param( param )
            DIS.write( f"{str} " )

        #when we don't have comment on line with 16bit immediate value, and that value is not a symbol
        if comment is None and params[0][0] == IMM16 and params[0][1] not in g_symbolsValue2Name:
            value = params[0][1]
            vall = value & 0xFF
            valh = value >> 8
            #if the value has both bytes printable, do add it as comment
            if vall in range(32,128) and valh in range(32,128):
                comment = f"\"{(chr(vall))}{(chr(valh))}\""

        #when we don't have comment on line with printable 8bit immediate value
        if comment is None and params[0][0] == IMM8:
            value = params[0][1]
            if value in range(32,128):
                comment = f"\"{(chr(value))}\""

    else:
        DIS.write( f" {mnemonic} " )
        if params is not None and params:
            for param in params:
                str = format_param( param )
                DIS.write( f"{str} " )

    if comment is not None:
       DIS.write( f"  #{comment}" )

    DIS.write( "\n" )
    if rec['mnemonic'] in [ 'Ret', 'Reti', 'Retff' ]:
        DIS.write( "\n" )
        is_end_of_function = True

    if rec['mnemonic'] == 'Jmpff' and 'Epilogue' in format_param( params[0] ):
        DIS.write( "\n" )
        is_end_of_function = True

    if params is not None and len(params) >= 1:
        if params[0][0] == ADDR24:
            g_crossref[params[0][1]] += 1

    if formatted_bytes:
        for str in formatted_bytes:
            DIS.write( ' ' * 18 )
            DIS.write( str + "\n" )

    return is_first_call_dest_instruction, is_end_of_function




table_instruction_mutations = [
    {
	#changes REG = R0 - R0 to REG = 0
        'from': [ { 'mnemonic': '=', 'param2v': 'R0 - R0' } ],
        'to': { 'param2': ( IMM8, 0 ) }
    },

    {
	#changes IO[Ix0] = to Ix0 =
        'from': [ { 'mnemonic': '=', 'param1t': IO, 'param1v': 'Ix0' } ],
        'to': { 'param1': ( REG, 'Ix0' ) }
    },

    {
        'from': [ 
		{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'Ix0.h', 'param2t': IMM8, 'store': { 'hi': 'param2v' } },
         	{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'Ix0.l', 'param2t': IMM8, 'store': { 'lo': 'param2v' } }
	],
        'to': { 'param1': ( REG, 'Ix0' ), 'param2': ( IMM16, lambda ctx: ( ctx['hi']<<8 | ctx['lo']) ) }
    },

    {
        'from': [ 
		{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'Ix1.h', 'param2t': IMM8, 'store': { 'hi': 'param2v' } },
         	{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'Ix1.l', 'param2t': IMM8, 'store': { 'lo': 'param2v' } }
	],
        'to': { 'param1': ( REG, 'Ix1' ), 'param2': ( IMM16, lambda ctx: ( ctx['hi']<<8 | ctx['lo']) ) }
    },

    {
        'from': [ 
		{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'R0.h', 'param2t': IMM8, 'store': { 'hi': 'param2v' } },
         	{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'R0.l', 'param2t': IMM8, 'store': { 'lo': 'param2v' } }
	],
        'to': { 'param1': ( REG, 'R0' ), 'param2': ( IMM16, lambda ctx: ( ctx['hi']<<8 | ctx['lo']) ) }
    },

    {
        'from': [ 
		{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'R1.h', 'param2t': IMM8, 'store': { 'hi': 'param2v' } },
         	{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'R1.l', 'param2t': IMM8, 'store': { 'lo': 'param2v' } }
	],
        'to': { 'param1': ( REG, 'R1' ), 'param2': ( IMM16, lambda ctx: ( ctx['hi']<<8 | ctx['lo']) ) }
    },

    {
        'from': [ 
		{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'Y0.h', 'param2t': IMM8, 'store': { 'hi': 'param2v' } },
         	{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'Y0.l', 'param2t': IMM8, 'store': { 'lo': 'param2v' } }
	],
        'to': { 'param1': ( REG, 'Y0' ), 'param2': ( IMM16, lambda ctx: ( ctx['hi']<<8 | ctx['lo']) ) }
    },

    {
        'from': [ 
		{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'Y1.h', 'param2t': IMM8, 'store': { 'hi': 'param2v' } },
         	{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'Y1.l', 'param2t': IMM8, 'store': { 'lo': 'param2v' } }
	],
        'to': { 'param1': ( REG, 'Y1' ), 'param2': ( IMM16, lambda ctx: ( ctx['hi']<<8 | ctx['lo']) ) }
    },

    {
        'from': [ 
		{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'X0.h', 'param2t': IMM8, 'store': { 'hi': 'param2v' } },
         	{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'X0.l', 'param2t': IMM8, 'store': { 'lo': 'param2v' } }
	],
        'to': { 'param1': ( REG, 'X0' ), 'param2': ( IMM16, lambda ctx: ( ctx['hi']<<8 | ctx['lo']) ) }
    },

    {
        'from': [ 
		{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'X1.h', 'param2t': IMM8, 'store': { 'hi': 'param2v' } },
         	{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'X1.l', 'param2t': IMM8, 'store': { 'lo': 'param2v' } }
	],
        'to': { 'param1': ( REG, 'X1' ), 'param2': ( IMM16, lambda ctx: ( ctx['hi']<<8 | ctx['lo']) ) }
    },

    {
        'from': [ 
		{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'X0', 'param2t': IMM8, 'store': { 'lo': 'param2v' } },
         	{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'X0.h', 'param2t': IMM8, 'store': { 'hi': 'param2v' } }
	],
        'to': { 'param1': ( REG, 'X0' ), 'param2': ( IMM16, lambda ctx: ( ctx['hi']<<8 | ctx['lo']) ) }
    },

    {
        'from': [ 
		{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'X1', 'param2t': IMM8, 'store': { 'lo': 'param2v' } },
         	{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'X1.h', 'param2t': IMM8, 'store': { 'hi': 'param2v' } }
	],
        'to': { 'param1': ( REG, 'X1' ), 'param2': ( IMM16, lambda ctx: ( ctx['hi']<<8 | ctx['lo']) ) }
    },

    {
        'from': [ 
		{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'R0', 'param2t': IMM8, 'store': { 'lo': 'param2v' } },
         	{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'R0.h', 'param2t': IMM8, 'store': { 'hi': 'param2v' } }
	],
        'to': { 'param1': ( REG, 'R0' ), 'param2': ( IMM16, lambda ctx: ( ctx['hi']<<8 | ctx['lo']) ) }
    },

    {
        'from': [ 
		{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'R1', 'param2t': IMM8, 'store': { 'lo': 'param2v' } },
         	{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'R1.h', 'param2t': IMM8, 'store': { 'hi': 'param2v' } }
	],
        'to': { 'param1': ( REG, 'R1' ), 'param2': ( IMM16, lambda ctx: ( ctx['hi']<<8 | ctx['lo']) ) }
    },

    {
        'from': [ 
		{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'Ix0', 'param2t': IMM8, 'store': { 'lo': 'param2v' } },
         	{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'Ix0.h', 'param2t': IMM8, 'store': { 'hi': 'param2v' } }
	],
        'to': { 'param1': ( REG, 'Ix0' ), 'param2': ( IMM16, lambda ctx: ( ctx['hi']<<8 | ctx['lo']) ) }
    },


    {
        'from': [ 
		{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'Y0', 'param2t': IMM8, 'store': { 'lo': 'param2v' } },
         	{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'Y0.h', 'param2t': IMM8, 'store': { 'hi': 'param2v' } }
	],
        'to': { 'param1': ( REG, 'Y0' ), 'param2': ( IMM16, lambda ctx: ( ctx['hi']<<8 | ctx['lo']) ) }
    },

    {
        'from': [ 
		{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'Y1', 'param2t': IMM8, 'store': { 'lo': 'param2v' } },
         	{ 'mnemonic': '=', 'param1t': REG, 'param1v': 'Y1.h', 'param2t': IMM8, 'store': { 'hi': 'param2v' } }
	],
        'to': { 'param1': ( REG, 'Y1' ), 'param2': ( IMM16, lambda ctx: ( ctx['hi']<<8 | ctx['lo']) ) }
    },

    {
        #changes
	#X0 = 0xLOLO
	#Push X0
	#X0 = 0x00HI
	#Push X0

	#to Push 0xHILOLO

        'from': [
		{ 'mnemonic': '=', 'param2t': IMM16, 'param1t': REG, 'param1v': 'X0', 'store': { 'lo': 'param2v' } },
		{ 'mnemonic': 'Push', 'param1t': REG, 'param1v': 'X0' },
		{ 'mnemonic': '=', 'param2t': IMM16, 'param2vc': lambda val: ( val >=0x28 and val <= 0x42 ), 'param1t': REG, 'param1v': 'X0', 'store': { 'hi': 'param2v' } },
		{ 'mnemonic': 'Push', 'param1t': REG, 'param1v': 'X0' }
	],
	'to': { 'mnemonic': 'Push', 'param1': ( ADDR24, lambda ctx: ( ctx['hi']<<16 | ctx['lo'] ) ), 'param2': None }
    },

    {
	#changes
	#R0 = 0xLOLO
	#R1 = 0x00HI
	#Push R0
	#Push R1

	#to Push 0xHILOLO

        'from': [
		{ 'mnemonic': '=', 'param2t': IMM16, 'param1t': REG, 'param1v': 'R0', 'store': { 'lo': 'param2v' } },
		{ 'mnemonic': '=', 'param2t': IMM16, 'param2vc': lambda val: ( val >=0x28 and val <= 0x42 ), 'param1t': REG, 'param1v': 'R1', 'store': { 'hi': 'param2v' } },
		{ 'mnemonic': 'Push', 'param1t': REG, 'param1v': 'R0' },
		{ 'mnemonic': 'Push', 'param1t': REG, 'param1v': 'R1' }
	],
	'to': { 'mnemonic': 'Push', 'param1': ( ADDR24, lambda ctx: ( ctx['hi']<<16 | ctx['lo'] ) ), 'param2': None }
    },

]

def mutate_one_instruction(pat,inst,ctx):
    pars = inst.get('parameters')
    inst_pars = 0
    if pars is not None:
        inst_pars = len(pars)

    for id, val in pat.items():
       if isinstance( val, tuple ):
           if callable( val[1] ):
               val = ( val[0], val[1](ctx) )

       if id=='param1':
           if inst_pars >= 1:
               inst['parameters'][0] = val
               continue
           raise Exception
       elif id=='param2':
           if inst_pars >= 2:
               if val == None:
                   #shortens to 1 parameter then
                   if inst_pars > 2:
                       raise Exception
                   inst['parameters'] = inst['parameters'][:1]
               else:
                   inst['parameters'][1] = val
               continue
           raise Exception
       elif id=='mnemonic':
           inst['mnemonic'] = val
           continue
       else:
           raise Exception( f"don't know how to mutate '{id}'" )
    return

def check_instruction_match(pat,inst,ctx):
    pars = inst.get('parameters')
    inst_pars = 0
    if pars is not None:
        inst_pars = len(pars)

    for id, val in pat.items():
        if id=='mnemonic':
            if inst['mnemonic']==val:
                continue
            return False
        elif id=='param1t':
            if inst_pars >= 1 and pars[0][0]==val:
                continue
            return False
        elif id=='param1v':
            if inst_pars >= 1 and pars[0][1]==val:
                continue
            return False
        elif id=='param2t':
            if inst_pars >= 2 and pars[1][0]==val:
                continue
            return False
        elif id=='param2v':
            if inst_pars >= 2 and pars[1][1]==val:
                continue
            return False
        elif id=='param2vc':
            if inst_pars >= 2:
                if not val(pars[1][1]):
                    return False
                continue
            return False
        elif id=='store':
            for var, par in val.items():
                if par=='param2v':
                    if inst_pars >= 2:
                        ctx[var]=pars[1][1]
                    else:
                        raise Exception
                else:
                    raise Exception( f"unknown src var name '{par}' in 'store'" )
        else:
            raise Exception( f"unknown id '{id}' to process" )

    #this place actually means we successfully matched it all
    return True

def instructions_mutator():
    global g_instruction_store

    #get max mutation length
    #this allows backtracking by max-1 instructions after succesful replacement
    #it's quite less than multipass processing, it's not single pass, but close
    max_mutation_len = 0
    for mutation in table_instruction_mutations:
        matcher = mutation[ 'from' ]
        max_mutation_len = max( len(matcher)-1, max_mutation_len )

    idx = 0
    cnt = len(g_instruction_store)

    while idx < cnt:
        max_ahead = cnt - idx

        for mutation in table_instruction_mutations:
            #we now have one mutation in hand
            matcher = mutation[ 'from' ]

            #only mutations short enough
            #this is valid most of the time (will only fail at the end of the instruction block)
            if len(matcher) <= max_ahead:
                #how many instructions must be matched for the replacement to take place
                to_match = len(matcher)
                #todo here is the place to check if there is jump in middle of instructions
                #it's wrong to join instructions in that place

                #track context between instructions and replacements here
                ctx = dict()
                for i in range(len(matcher)):
                    if check_instruction_match( matcher[ i ], g_instruction_store[ idx + i ], ctx ):
                        to_match -= 1
                    else:
                        break

                #all of the conditions matched
                if to_match == 0:
                    #create new instruction, current logic is to leave the first one and replace its params
                    #not even the copy
                    inst = g_instruction_store[ idx ]
                    mutate_one_instruction( mutation[ 'to' ], inst, ctx )

                    #we store the raw instruction bytes intact
                    #mostly for checking the validity if needed
                    all_words = []
                    for i in range(len(matcher)):
                        all_words += g_instruction_store[idx+i]['words']
                    inst['words'] = all_words

                    #remove replaced instructions
                    #logic is currently hardcoded N-to-1
                    del g_instruction_store[idx+1:idx+len(matcher)] 
                    cnt = len(g_instruction_store)

                    #backtrack
                    idx = max( 0, idx - max_mutation_len)
                    continue
            #endif
        idx += 1
    return

def instructions_disassembly(words):
    idx = 0
    idx_end = len(words)

    while idx < idx_end:
        word1 = words[idx]
        idx += 1

        high = word1 >> 8;
        low = word1 & 0xFF;

        # Call
        if high & 0b_1000_0000 == 0:
            abs_addr = ((high & 0b_0111_1111) << 8) + low
            store_instruction( [word1], "Call", [ (ADDR16, abs_addr ) ], None )
        # Jump
        elif ((high >> 4) & 0b_0000_1111) == 0b_1000:
            offset = signed12( ((high & 0b_0000_1111) << 8) + low ) # Offset is signed !
            store_instruction( [word1], 'Jmp', [ ( ADDR24, g_PC+1+offset) ], None )
        # Jump Condition
        elif ((high >> 4) & 0b_0000_1111) == 0b_1001:
            cond = high & 0b_0000_1111
            offset = signed8(low)   # Offset is signed !
            mnemonic = 'J' + condsuffix(cond)
            comment = None
            if -10 <= offset <= 10:
                comment = f"{offset} lines from here"
            store_instruction( [word1], mnemonic, [ ( ADDR24, g_PC+1+offset) ], comment )
        # RW Mem (direct)
        elif( high & 0b_1110_0000 ) == 0b_1010_0000:
            r = (high & 0b_0001_0000) >> 4       # direction r=0: DM(imm) <= Reg      r=1: Reg <= DM(imm)
            hash = (high & 0b_0000_1000) >>3    # Offset[8]
            reg = high & 0b_0000_0111
            offset = (hash << 8) | low
            if r:
                store_instruction( [word1], '=', [ ( REG, register(reg) ), ( DM, offset ) ], None )
            else:
                store_instruction( [word1], '=', [ ( DM, offset ), ( REG, register(reg) ) ], None )
        # Load Immediate
        elif ((high >> 5) & 0b_0000_0111) == 0b_110 and ((high >> 3) & 0b_0000_0011) != 0b_01:
            L = (high & 0b_0001_1000) >> 3       # L=00: Load High, Keep Low     L=10: Keep High, Load Low       L=11: Clear High, Load Low
            reg1 = high & 0b_0000_0111
            imm = low
            store_instruction( [word1], '=', [ ( REG, register1(reg1) + hilo(L) ), ( IMM8, imm ) ], None )
        # AU(2) To Mem
        elif ((high >> 3) & 0b_0001_1111) == 0b_11001 and ((low >> 7) & 0b_0000_0001) == 0b_0:
            A = (high & 0b_0000_0110) >> 1       # A=00: No Change  A=01: By Modifier   A=10: +1    A=11: -1
            Ix = (high & 0b_0000_0001)           # 0: Ix0   1: Ix1
            Xop = (low & 0b_0110_0000) >> 5
            AU = (low & 0b_0001_1100) >> 2
            Yop = (low & 0b_0000_0011)
            modif = modifier(A)                  # Modifier indicates how the data address (indirect register Ix/y) is incremented after the operation (not incremented, +1, -1, +modifier register lm)
            first_operand = operand1(Xop)
            second_operand = operand2(Yop)
            # FIXME What is C ??? --> Carry ???
            if AU == 0b_000:
                operation = '%s + 1' % (first_operand)
            elif AU == 0b_001:
                operation = '%s - 1' % (first_operand)
            elif AU == 0b_010:
                operation = '%s + %s' % (first_operand, second_operand)
            elif AU == 0b_011:
                operation = '%s + %s + C' % (first_operand, second_operand)
            elif AU == 0b_100:
                operation = '%s - %s' % (first_operand, second_operand)
            elif AU == 0b_101:
                operation = '%s - %s + C - 1' % (first_operand, second_operand)
            elif AU == 0b_110:
                operation = '-%s + %s' % (first_operand, second_operand)
            elif AU == 0b_111:
                operation = '-%s + %s + C - 1' % (first_operand, second_operand)
            store_instruction( [word1], '=', [ (RAM, "Ix" + str(Ix) + modif ), ( STR, operation ) ], None )
        # LU(1)
        elif ((high >> 3) & 0b_0001_1111) == 0b_11001 and ((low >> 7) & 0b_0000_0001) == 0b_1 and ((low >> 2) & 0b_0000_0001) == 0b_0:
            reg = high & 0b_0000_0111
            Xop = (low & 0b_0110_0000) >> 5
            LU1 = (low & 0b_0001_1000) >> 3
            Yop = (low & 0b_0000_0011)
            first_operand = operand1(Xop)
            second_operand = operand2(Yop)
            if LU1 == 0b_00:
                operation = '%s AND %s' % (first_operand, second_operand)
            elif LU1 == 0b_01:
                operation = '%s OR %s' % (first_operand, second_operand)
            elif LU1 == 0b_10:
                operation = '%s XOR %s' % (first_operand, second_operand)
            elif LU1 == 0b_11:
                operation = 'NOT %s' % (first_operand)
            store_instruction( [word1], '=', [ ( REG, register(reg) ), ( STR, operation) ], None )
        # LU(2)
        elif ((high >> 3) & 0b_0001_1111) == 0b_11001 and ((low >> 7) & 0b_0000_0001) == 0b_1 and ((low >> 2) & 0b_0000_0001) == 0b_1:
            _f = high & 0b_0000_0001              # 0: r0    1: r1
            Cst_x = ((high & 0b_0000_0110) << 1) | ((low & 0b_0110_0000) >> 5)
            LU2 = (low & 0b_0001_1000) >> 3
            Yop = (low & 0b_0000_0011)
            operand = operand2(Yop)
            mnemonic = lu2(LU2)
            store_instruction( [word1], '=', [ (REG, "R"+ str(_f) ), ( STR, mnemonic + '.' + str(Cst_x) ), ( REG, operand) ], None )
        # RW SRAM (indirect)
        elif ((high >> 3) & 0b_0001_1111) == 0b_11100 and ((low >> 7) & 0b_0000_0001) == 0b_0 and (low & 0b_0000_0011) == 0b_00:
            reg = high & 0b_0000_0111
            r = (low & 0b_0100_0000) >> 6        # r=0: RAM(offset) <= Reg      r=1: Reg <= RAM(offset)
            A = (low & 0b_0011_0000) >> 4        # A=00: No Change  A=01: By Modifier   A=10: +1    A=11: -1
            Ixy = (low & 0b_0000_1100) >> 2      # 00: Ix0   01: Ix1    10: Iy0     11: Iy1
            modif = modifier(A)                  # Modifier indicates how the data address (indirect register Ix/y) is incremented after the operation (not incremented, +1, -1, +modifier register lm)
            ind = indirect(Ixy)
            if r:
                store_instruction( [word1], '=', [ ( REG, register(reg) ), ( RAM, ind+modif ) ], None )
            else:
                store_instruction( [word1], '=', [ ( RAM, ind+modif ), ( REG, register(reg) ) ], None )
        # Load ROM (indirect)
        elif ((high >> 3) & 0b_0001_1111) == 0b_11100 and ((low >> 6) & 0b_0000_0011) == 0b_01 and (low & 0b_0000_0011) == 0b_01:
            reg = high & 0b_0000_0111
            A = (low & 0b_0011_0000) >> 4        # A=00: No Change  A=01: By Modifier   A=10: +1    A=11: -1
            Ixy = (low & 0b_0000_1100) >> 2      # 00: Ix0   01: Ix1    10: Iy0     11: Iy1
            modif = modifier(A)                  # Modifier indicates how the data address (indirect register Ix/y) is incremented after the operation (not incremented, +1, -1, +modifier register lm)
            ind = indirect(Ixy)
            store_instruction( [word1], '=', [(REG, register(reg)), ( ROM, ind+modif ) ], None )
        # Shift index
        elif ((high >> 3) & 0b_0001_1111) == 0b_11100 and ((low >> 6) & 0b_0000_0011) == 0b_01 and (low & 0b_0000_0111) == 0b_010:
            reg = high & 0b_0000_0111
            _f = (low & 0b_0010_0000) >> 5       # 0: r0    1: r1
            sf = (low & 0b_0001_1000) >> 3       # 00: Shift Left Sign Extension    01: A/L Shift Left  10: A Shift Right   11: L Shift Right
            mnemonic = shift(sf)
            # Number of bits to shift is determined by the ShIdx I/O (0x003e)
            store_instruction( [word1], '=', [ (REG, 'R'+str(_f) ), ( STR, '%s.Idx %s' % (mnemonic, register(reg)) ) ], None )
        # I/O (1)
        elif ((high >> 3) & 0b_0001_1111) == 0b_11100 and ((low >> 7) & 0b_0000_0001) == 0b_1:
            r = (high & 0b_0000_0100) >> 2        # r=0: IO(offset) <= RegL      r=1: RegL <= IO(offset)
            regL = (high & 0b_0000_0011)
            offset = low & 0b_0111_1111
            label = ioRegisterLabel(offset)
            labelExt = None
            labelArr = label.split( '|', 2 )
            if len(labelArr) > 1:
                 label, labelExt = labelArr
            else:
                 label, labelExt = labelArr[0], None
            comment = ''
            if( labelExt ):
                comment = 'I/O register = %s' % (labelExt)
            if r:
                store_instruction( [word1], '=', [( REG, registerL(regL)), ( IO, label ) ], comment )
            else:
                store_instruction( [word1], '=', [ ( IO, label ), ( REG, registerL(regL)) ], comment )
        # AU(1)
        elif ((high >> 3) & 0b_0001_1111) == 0b_11101:
            regDst = high & 0b_0000_0111
            regSrc = (low & 0b_1110_0000) >> 5
            AU = (low & 0b_0001_1100) >> 2
            Yop = (low & 0b_0000_0011)
            first_operand = register(regSrc)
            second_operand = operand2(Yop)
            if AU == 0b_000:
                operation = '%s + 1' % (first_operand)
            elif AU == 0b_001:
                operation = '%s - 1' % (first_operand)
            elif AU == 0b_010:
                operation = '%s + %s' % (first_operand, second_operand)
            elif AU == 0b_011:
                operation = '%s + %s + C' % (first_operand, second_operand)
            elif AU == 0b_100:
                operation = '%s - %s' % (first_operand, second_operand)
            elif AU == 0b_101:
                operation = '%s - %s + C - 1' % (first_operand, second_operand)
            elif AU == 0b_110:
                operation = '-%s + %s' % (first_operand, second_operand)
            elif AU == 0b_111:
                operation = '-%s + %s + C - 1' % (first_operand, second_operand)
            store_instruction( [ word1], '=', [ ( REG, register(regDst) ), ( STR, operation) ], None )
        # MAC
        elif ((high >> 3) & 0b_0001_1111) == 0b_11110:
            MAC = high & 0b_0000_0111
            M = (low & 0b_1000_0000) >> 7        # 0: simple MAC    1: multiple-function
            Ix = (low & 0b_0100_0000) >> 6       # 0: Ix0   1: Ix1
            A = (low & 0b_0011_0000) >> 4        # A=00: No Change  A=01: By Modifier   A=10: +1    A=11: -1
            DXY = (low & 0b_0000_1100) >> 2      # 00: X0   01: X1  10: Y0  11: Y1
            X = (low & 0b_0000_0010) >> 1        # 0: X0    1: X1
            Y = low & 0b_0000_0001               # 0: Y0    1: Y1
            first_operand = operand1(X)
            second_operand = operand2(Y)
            if MAC == 0b_000:
                operation = '%s * %s (IS)' % (first_operand, second_operand)
            elif MAC == 0b_001:
                operation = 'MR + %s * %s (IS)' % (first_operand, second_operand)
            elif MAC == 0b_010:
                operation = 'MR - %s * %s (IS)' % (first_operand, second_operand)
            elif MAC == 0b_011:
                # FIXME Unsupported
                operation = 'TBD'
            elif MAC == 0b_100:
                operation = '%s * %s (FS)' % (first_operand, second_operand)
            elif MAC == 0b_101:
                operation = 'MR + %s * %s (FS)' % (first_operand, second_operand)
            elif MAC == 0b_110:
                operation = 'MR - %s * %s (FS)' % (first_operand, second_operand)
            elif MAC == 0b_111:
                # FIXME Unsupported
                operation = 'TBD'
            # Optional second (parallel) operation (load from RAM)
            if M == 0b_0:
                operation2 = ''
            elif M == 0b_1:
                modif = modifier(A)              # Modifier indicates how the data address (indirect register Ix/y) is incremented after the operation (not incremented, +1, -1, +modifier register lm)
                operation2 = ', %s = RAM[Ix%s%s]' % (dxy(DXY), Ix, modif)
            store_instruction( [word1], 'MR =', [ ( STR, '%s%s' % (operation, operation2) ) ], None )
        # Reg Move
        elif high == 0b_1111_1000 and (low & 0b_0000_0011) == 0b_00:
            regSrc = (low & 0b_1110_0000) >> 5
            regDst = (low & 0b_0001_1100) >> 2
            store_instruction( [word1], '=', [ ( REG, register(regDst) ), ( REG, register(regSrc)) ], None )
        # Push / Pop
        elif high == 0b_1111_1000 and (low & 0b_0001_1110) >> 1 == 0b_0001:
            reg = (low & 0b_1110_0000) >> 5
            U = low & 0b_0000_0001               # 0: push  1: pop
            mnemonic = pushpop(U)
            store_instruction( [ word1 ], mnemonic, [ ( REG, register(reg) ) ], None )
        # Shift
        elif ((high >> 1) & 0b_0111_1111) == 0b_111_1101:
            _f = high & 0b_0000_0001             # 0: r0    1: r1
            reg = (low & 0b_1110_0000) >> 5
            sf = (low & 0b_0001_1000) >> 3       # 00: Shift Left Sign Extension    01: A/L Shift Left  10: A Shift Right   11: L Shift Right
            sh = low & 0b_0000_0111              # Number of bits to shift (000: 1, 001: 2, ...)
            mnemonic = shift(sf)
            store_instruction( [word1], '=', [ ( REG, 'R' + str(_f) ), ( STR, mnemonic + '.' + str(sh+1) ), ( REG, register(reg) ) ], None )
        # I/O (2) + Push / Pop I/O
        elif high == 0b_1111_1100 and (low & 0b_1000_0000) >> 7 == 0b_1:
            r = (low & 0b_0100_0000) >> 6        # 0: Push IO(offset)   1: Pop IO(offset)
            offset = low & 0b_0011_1111
            mnemonic = pushpop(r)

            label = ioRegisterLabel(offset)
            labelExt = None
            labelArr = label.split( '|', 2 )
            if len(labelArr) > 1:
                 label, labelExt = labelArr
            else:
                 label, labelExt = labelArr[0], None
            comment = ''
            if( labelExt ):
                comment = 'I/O register = %s' % (labelExt)

            store_instruction( [word1], mnemonic, [ ( IO, label) ], comment )
        # Reserved  FIXME Should throw en error ???
        elif high == 0b_1111_1100 and (low & 0b_1000_0000) >> 7 == 0b_0:
            store_instruction( [word1], 'Reserved', None, None )
        # Callff (2-words instruction)
        elif high == 0b_1111_1101:
            abs_addr_high = low
            
            word2 = words[ idx ]
            idx += 1

            #print('%s %s' % (hex(second_word[0],2), hex(second_word[1],2)))
            abs_addr_low = word2
            abs_addr = (abs_addr_high << 16) | abs_addr_low
            store_instruction( [word1, word2], 'Callff', [ ( ADDR24, abs_addr ) ], None )
            pointer_move(2)
        # Jumpff (2-words instruction)
        elif high == 0b_1111_1110:
            abs_addr_high = low

            word2 = words[ idx ]
            idx += 1

            abs_addr_low = word2
            abs_addr = (abs_addr_high << 16) | abs_addr_low
            store_instruction( [ word1, word2], 'Jmpff', [ ( ADDR24, abs_addr ) ], None )
            pointer_move(2)
        # Do0   FIXME No operation documentation??? Should fail ???
        elif high == 0b_1111_1100 and (low & 0b_1100_0000) >> 6 == 0b_00:
            cntV = low & 0b_0011_1111
            store_instruction( [word1], 'Do0', [ ( IMM8, cntV ) ], None )
        # Do1   FIXME No operation documentation??? Should fail ???
        elif high == 0b_1111_1100 and (low & 0b_1100_0000) >> 6 == 0b_01:
            cntV = low & 0b_0011_1111
            store_instruction( [word1], 'Do1', [ ( IMM8, cntV ) ], None )
        # Loop0 FIXME No operation documentation??? Should fail ???
        elif high == 0b_1111_1111 and low == 0b_1111_1100:
            store_instruction( [word1], 'Loop0', None, None )
        # Loop1 FIXME No operation documentation??? Should fail ???
        elif high == 0b_1111_1111 and low == 0b_1111_1110:
            store_instruction( [word1], 'Loop1', None, None )
        # Ret                                
        elif high == 0b_1111_1111 and low == 0b_0100_0000:
            store_instruction( [word1], 'Ret', None, None )
        # Reti
        elif high == 0b_1111_1111 and low == 0b_0100_0001:
            store_instruction( [word1], 'Reti', None, None )
        # Retff
        elif high == 0b_1111_1111 and low == 0b_0100_0010:
            store_instruction( [word1], 'Retff', None, None )
        # ICEC  FIXME Unused ???
        elif high == 0b_1111_1111 and low == 0b_1111_1101:
            store_instruction( [word1], 'ICE', None, 'ICE Call Function')
        # NOP
        elif high == 0b_1111_1111 and low == 0b_1111_1111:
            store_instruction( [word1], 'Nop', None, None )
        # DisSPSW   FIXME Undocumented ?! Should fail ??? (Clear SCR.SPSW)
        elif high == 0b_1111_1111 and low == 0b_0000_0001:
            store_instruction( [word1], 'DisSPSW', None, None )
        # EnSPSW    FIXME Undocumented ?! Should fail ??? (Enable SCR.SPSW write)
        elif high == 0b_1111_1111 and low == 0b_1111_1111:
            store_instruction( [word1], 'EnSPSW', None, None )
        # EMAC      FIXME CONFLICTS WITH MAC OPERATION (0b_11110...) ?!
        elif ((high >> 3) & 0b_1111_1000) == 0b_11110 and (low & 0b_01000000) >> 6 == 0b_1:
            MAC = high & 0b_0000_0111
            EM = (low & 0b_1000_0000) >> 7       # 0: simple MAC    1: multiple-function
            AmX = (low & 0b_0010_0000) >> 5      # 0: ImxL (Linear)     1: ImxC (Circular)
            AmY = (low & 0b_0001_0000) >> 4      # 0: ImyL (Linear)     1: ImyC (Circular)
            DmX = (low & 0b_0000_1000) >> 3      # 0: X0    1: X1
            DmY = (low & 0b_0000_0100) >> 2      # 0: Y0    1: Y1
            X = (low & 0b_0000_0010) >> 1        # 0: X0    1: X1
            Y = low & 0b_0000_0001               # 0: Y0    1: Y1
            # TODO Multiple Functions with Double-Fetched
            # When MMR register (0x0017) bit13 is set, MAC operation should enable Double Fetch Instruction
            # -> same binary instruction, different behaviour and parameter layout...
            store_instruction( [word1], 'EMAC', None, None )
        # Unhandled opcode
        else:
            store_instruction( [word1], '**UNKNOWN**', None, None )
            # TODO Should break and throw an error?

        pointer_move(2)
    #loop ends


def extract_prologue_info( r_PC, idx ):
    prologue_type = "naked"
    registers = dict()
    prologue_pars = None
    locals = dict()

    max_inst = 30
    idx_end = min( idx + max_inst, len(g_instruction_store ) )
    while idx < idx_end:
        inst = g_instruction_store[ idx ]

        mnem = inst['mnemonic']
        parcnt = 0
        if 'parameters' in inst and inst['parameters'] is not None:
            parcnt = len( inst['parameters'] )

        #print( f"{idx}/{(inst['PC']):06x} parcnt:{parcnt} {inst}" )

        if mnem=='Retff':
            break
        elif mnem=='Callff':
            sym = g_symbolsValue2Name[ inst['parameters'][0][1] ]
            if sym.startswith( 'FunctionPrologue' ):
                prologue_type = sym
                prologue_pars = ", ".join(f"{name}=0x{value:04x}" for name, value in sorted(registers.items()))
        elif mnem=='=' and inst['parameters'][0][0]==REG and ( inst['parameters'][1][0]==IMM8 or inst['parameters'][1][0]==IMM16 ):
            registers[inst['parameters'][0][1]] = inst['parameters'][1][1]
        elif mnem=='=' and inst['parameters'][0][0]==DM and inst['parameters'][1][0]==REG and inst['parameters'][0][1]>=0x17:
            locals[inst['parameters'][0][1]] = inst['parameters'][1][1]
        else:
            #todo is this logic sound?
            break
        idx += 1

    g_calls[r_PC]['prologue_type'] = prologue_type
    g_calls[r_PC]['prologue_pars'] = prologue_pars
    g_calls[r_PC]['prologue_locals'] = ", ".join(f"DM[0x{value:03x}]={reg}" for value, reg in sorted(locals.items()))

def extract_epilogue_info( PC_last_start, idx ):
    epilogue_type = "unknown";
    if PC_last_start is None:
        return

    inst = g_instruction_store[ idx ]
    mnem = inst['mnemonic']

    inst = g_instruction_store[ idx ]
    if mnem=='Retff':
        epilogue_type = 'Retff'
    elif mnem=='Jmpff':
        sym = g_symbolsValue2Name[ inst['parameters'][0][1] ]
        if sym.startswith( 'FunctionEpilogue' ):
            epilogue_type = sym

    g_calls[ PC_last_start ]['epilogue_type'] = epilogue_type
    g_calls[ PC_last_start ]['epilogue_address'] = inst['PC']

def instructions_printer():
    global g_last_function_start

    idx = 0
    while idx < len(g_instruction_store):
        instr = g_instruction_store[idx]

        is_first_call_dest_instruction, is_last_instruction = print_stored_instruction(instr)
        #print( f"in i_p: {is_first_call_dest_instruction} {is_last_instruction} {(instr['PC']):06x}" )
        if is_first_call_dest_instruction:
            g_last_function_start = instr['PC']
            extract_prologue_info( instr['PC'], idx )

        if is_last_instruction:
            extract_epilogue_info( g_last_function_start, idx )
            g_last_function_start = None
        idx += 1
    #endwhile

# === Entry point ===

filename = sys.argv[1] if len(sys.argv) > 1 else "mapfile.def"
mapfile_parse( filename )
