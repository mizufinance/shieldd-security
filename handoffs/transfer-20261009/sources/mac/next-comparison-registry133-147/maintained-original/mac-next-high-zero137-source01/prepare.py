from pathlib import Path
import re
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work')
def require(ok,msg):
 if not ok:raise ValueError(msg)
mp={1110:1371,1111:1372,33770:33778,33771:33779,33772:33780,33773:33781,11032:11040,440:448,179023:179287,1069:1333,45:53}
def mapped(t):return re.sub(r'\b(?:'+'|'.join(map(str,mp))+r')\b',lambda m:str(mp[int(m[0])]),t)
S=W/'mac-next-high-zero137-source01';require(not S.exists(),'fresh');S.mkdir();t=(W/'mac-registry-high-zero126-data-source07/template.lean').read_text().replace('CapturedHighLimbShared124','CapturedNextHighLimb133').replace('CapturedRegistryHighLimb120','CapturedNextHighLimb133').replace('CapturedHighZero126Data','CapturedNextHighZero137Data').replace('CapturedAssertions50B0004','CapturedAssertions50B0005');t=mapped(t)
# Root-to-leaf path now enters second256 leaf of the 1024..1535 pair.
t=t.replace('rw [if_pos (show 1333+index-1024<256 by omega)]','rw [if_neg (show ¬1333+index-1024<256 by omega)]').replace('1333+index-1024=53+index','1333+index-1024-256=53+index').replace('block.actual (1333+index-1024)=_','block.actual (1333+index-1024-256)=_');(S/'template.lean').write_text(t)
g=(W/'mac-registry-high-zero126-data-source07/generate.py').read_text().replace('CapturedHighZero126Data','CapturedNextHighZero137Data').replace('mac-registry-high-zero126-data01','mac-next-high-zero137-data01').replace('144577','144573').replace('f26157e0698fb78114c722852ef839772a913e9ab3c667f22935572cdf660ac3','79b1d51bccf7e12e2669e21012db1792c88ec667986e7a14072239ed34d48fd6').replace('11032..11035','11040..11043').replace('179023..179025','179287..179289').replace('first high-limb','second high-limb');(S/'generate.py').write_text(g);(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
S=W/'mac-next-high-zero138-source01';require(not S.exists(),'fresh');S.mkdir();t=(W/'mac-registry-high-zero126-source08/template.lean').read_text().replace('CapturedHighLimbShared124','CapturedNextHighShared136').replace('CapturedRegistryHighLimb120','CapturedNextHighLimb133').replace('CapturedHighZero126Data','CapturedNextHighZero137Data').replace('CapturedHighZero126','CapturedNextHighZero138').replace('CapturedAssertions50B0004','CapturedAssertions50B0005');t=mapped(t);(S/'template.lean').write_text(t);g=(W/'mac-registry-high-zero126-source08/generate.py').read_text().replace('CapturedHighZero126Data','CapturedNextHighZero137Data').replace('CapturedHighZero126','CapturedNextHighZero138');# main generator source08 no data decoding placeholders
require('@AR@'not in t,'main references already qualified data')
(S/'generate.py').write_text(g);(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
