
Zde jsou nástroje na vytvoření disassemblovaného firmware za pomocí semiautomatického disassembleru.
Vlastní kód disassembleru pochází z tohoto repository: https://github.com/marian-m12l/s9ke-toolchain ale již tvoří nejvýše polovinu
tohoto programu - přidán byl mutátor instrukcí, podpora symbolů, i automatických, křížové odkazy atp. Vstupem pro dissector.py je ručně vytvořený 
'popis' firmware, který naznačuje disassembleru, jak postupně procházet jednotlivé bloky firmware - zabývá se jen 1.bin částí, kde je vlastní kód,
v kódu je však vidět závislosti na dalších částech.

dissector.py - disassembler

mapfile_old.def - obsahuje popis druhého nejstaršího firmware (tento soubor již nebude aktualizován)

mapfile.def - obsahuje popis nejnovějšího firmware

rom_dumper.asm - kód pro vydumpování ROMky z DSP Sonix