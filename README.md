# albituzka
Reverzní inženýrství Albi Kouzelného čtení.

V adresáři docs je popis formátu BNL a obsahu firmware.

V adresáři tools pak nástroje k rozebrání a složení BNL souboru, generátor OID kódů a další nástroje.

V adresáři test je ukázkový soubor pro vlastní knihu spolu s podklady

English:
Reverse engineering of BNL files used for Albi electronic pen. Works also for files found on SpeakItBooks.com. To check if this description is valid for your BNL files, XOR first two 32bit DWORDs, you should get 0x200 in little endian.


Disclaimer:
Toto je _neoficiální_ a _nekomerční_ projekt, který _nijak_ nesouvisí se společností Albi.

Společnost Albi není autorem tohoto obsahu, nepodílí se na jeho vývoji, nepodporuje jej a nenese za něj žádnou odpovědnost. Všechny názvy produktů, ochranné známky a loga patří jejich příslušným vlastníkům a jsou použity pouze pro identifikační účely.

Cílem tohoto projektu je technická analýza a dokumentace s edukativním účelem. Veškeré poznatky jsou výsledkem nezávislého zkoumání zakoupeného zařízení a nejsou nijak spojeny s výrobcem či distributorem.