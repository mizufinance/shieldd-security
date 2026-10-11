from pathlib import Path
import re
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-next-low-limb140-data01'
def require(ok,msg):
 if not ok:raise ValueError(msg)
require(not S.exists(),'fresh');S.mkdir();s=(W/'mac-registry-low-limb129-data01/extract.py').read_text()
mp={125890:128213,126791:129114,126145:128468,126401:128724,471:726,216:471,1112:1373,1113:1374,1114:1375,1242:1503,1072:1336,599:854,344:599};s=re.sub(r'\b(?:'+'|'.join(map(str,mp))+r')\b',lambda m:str(mp[int(m[0])]),s).replace('asset_low versus registry_value_low','next_low versus asset_low').replace('179026..179156','179290..179420');(S/'extract.py').write_text(s);(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
