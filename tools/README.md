
### Prostředí
Všechny nástroje byly napsány pod Windows 10, na ActiveState Perlu 5.24.3. Pro běh na jiném OS by neměly být teoreticky
potřebné žádné úpravy. Je možné, že bude nutno doinstalovávat některé moduly, které nejsou typickou součástí instalace,
např. Imager, Imager::Fill, YAML, MP3::Info a další. Jakým způsobem doinstalovat moduly lze dohledat v dokumentaci.
Byl proveden i test na Windows 7, Strawberry Perl, vše je funkční. První pokus o dokumentaci skriptů lze dohledat v docs/albituzka_nastroje.pdf
Všechny nástroje jsou pouze příkazovo-řádkové, nemají žádné grafické rozhraní.

### Popis nástrojů v tomto adresáři

creator/bnl_creator.pl - generuje BNL soubor ze mnoha mp3 souborů a bnl.yaml. Tyto lze získat pomocí bnl_dis.pl z existujícího bnl souboru

disassembler/bnl_dis.pl - rozebírá BNL soubor na mp3 soubory a bnl.yaml.

firmware_cutter/fw_cutter.pl - identifikuje a rozřezává obsah firmware souboru update.chp

firmware_disasm - nástroj pro disassemblování firmware

oid_generator/oid_png_generator - generuje vytisknutelný png soubor s jedním OID kódem. Nebo více ze vstupního souboru

oid_rawtable/oid_table_extract - extrahuje konverzní tabulku OID 2.0 raw kódů na interní kódy z nástroje OidCreator
