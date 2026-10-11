from pathlib import Path
import re
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-next-high-zero137-data01'
def require(ok,msg):
 if not ok:raise ValueError(msg)
require(not S.exists(),'fresh');S.mkdir();s=(W/'mac-registry-high-zero126-data01/extract.py').read_text();mp={125375:127698,125889:128212,125886:128209,125884:128207,125885:128208,33770:33778,33771:33779,33772:33780,33773:33781,599:854,344:599,1069:1333,1110:1371,1111:1372,1112:1373,11032:11040,11036:11044}
s=re.sub(r'\b(?:'+'|'.join(map(str,mp))+r')\b',lambda m:str(mp[int(m[0])]),s).replace('asset-high minus registry-high','next-high minus asset-high').replace('11032..11035','11040..11043').replace('179023..179025','179287..179289');(S/'extract.py').write_text(s);(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
