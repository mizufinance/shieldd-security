from pathlib import Path
import re,hashlib
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work')
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
D=W/'mac-next-high-limb133-data01/selected-data01.json';require(pin(D)['sha256']=='41aa16d21b03016538c27b4ce1607acaf41636bffa11690ae53a017a2a4c275a','frozen actual DATA')
S=W/'mac-next-high-limb133-source01';require(not S.exists(),'fresh');S.mkdir();t=(W/'mac-registry-low-limb129-source01/template.lean').read_text().replace('CapturedRegistryLowLimb129','CapturedNextHighLimb133')
a=t.index('theorem full_position');prefix=t[:a];mp={1114:1244,128:127,471:854,216:599,129:128,1112:1242,1113:1243,131:130,48:179};prefix=re.sub(r'\b(?:'+'|'.join(map(str,mp))+r')\b',lambda m:str(mp[int(m[0])]),prefix)
body=t[a:].replace('179026','179157').replace('1072','1203').replace('index<131','index<130').replace('48+index','179+index')
t=prefix+body;(S/'template.lean').write_text(t);g=(W/'mac-registry-low-limb129-source01/generate.py').read_text().replace('CapturedRegistryLowLimb129','CapturedNextHighLimb133');a=g.index('selected_data=');b=g.index(',generator=',a);g=g[:a]+'selected_data='+repr(pin(D))+g[b:];(S/'generate.py').write_text(g);(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
S=W/'mac-next-high-limb134-source01';require(not S.exists(),'fresh');S.mkdir();t=(W/'mac-registry-high-limb121-source03/template.lean').read_text().replace('CapturedRegistryHighLimb120','CapturedNextHighLimb133').replace('CapturedRegistryHighLimb121','CapturedNextHighLimb134');mp={981:1242,982:1243,983:1244,1110:1371,178893:179157};t=re.sub(r'\b(?:'+'|'.join(map(str,mp))+r')\b',lambda m:str(mp[int(m[0])]),t);(S/'template.lean').write_text(t);g=(W/'mac-registry-high-limb121-source03/generate.py').read_text().replace('CapturedRegistryHighLimb121','CapturedNextHighLimb134');(S/'generate.py').write_text(g);(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
