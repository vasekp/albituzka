
Zde jsou dva disassemblované firmware za pomocí semiautomatického disassembleru.
Vlastní kód disassembleru pochází z tohoto repository: https://github.com/marian-m12l/s9ke-toolchain ale již tvoří nejvýše polovinu
tohoto programu - přidán byl mutátor instrukcí, podpora symbolů, i automatických, křížové odkazy atp.

dissector.py - disassembler

mapfile_old.def - obsahuje popis druhého nejstaršího firmware

disassembly_old.asm - výstup dissector.py za použití mapfile_old.def


mapfile.def - obsahuje popis nejnovějšího firmware

disassembly.asm - výstup dissector.py za použití mapfile.def. Tento soubor je ještě stále "work in progress".

