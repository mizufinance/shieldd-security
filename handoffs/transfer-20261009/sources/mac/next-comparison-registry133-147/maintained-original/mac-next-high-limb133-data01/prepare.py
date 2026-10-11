from pathlib import Path
import re
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');D=W/'mac-next-high-limb133-data01'
def require(ok,msg):
 if not ok:raise ValueError(msg)
require(not D.exists(),'fresh DATA');D.mkdir();s=(W/'mac-registry-high-limb120-data02/extract.py').read_text()
for a,b in [('124480','126803'),('125374','127697'),('124733','127056'),('124987','127310'),('idx=939+j','idx=1203+j')]:
 require(a in s,'exact source pattern '+a);s=s.replace(a,b)
mp={599:854,344:599,981:1242,982:1243,983:1244,1110:1371,726:981,471:726};s=re.sub(r'\b(?:'+'|'.join(map(str,mp))+r')\b',lambda m:str(mp[int(m[0])]),s)
s=s.replace('first127-bit bounded limb asset_high versus registry_value_high','second127-bit bounded limb next_high versus asset_high').replace('178893..179022','179157..179286').replace('original_input_high_asset','original_input_high_next').replace('original_input_high_value','original_input_high_asset');(D/'extract.py').write_text(s);(D/'prepare.py').write_bytes(Path(__file__).read_bytes())
