from pathlib import Path
import re,json,hashlib
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work')
for old,stage,oldname,newname,olddata,newdata,oldproof,newproof,m in [
('mac-high-comparison-sound149-source02','mac-next-high-sound153-source01','CapturedHighComparisonSound149','CapturedNextHighSound153','CapturedRegistryHighLimb120','CapturedNextHighLimb133','CapturedRegistryHighLimb121','CapturedNextHighLimb134',{'981':'1242','982':'1243','983':'1244'}),
('mac-low-comparison-sound151-source01','mac-next-low-sound154-source01','CapturedLowComparisonSound151','CapturedNextLowSound154','CapturedRegistryLowLimb129','CapturedNextLowLimb140','CapturedRegistryLowLimb130','CapturedNextLowLimb141',{'1112':'1373','1113':'1374','1114':'1375'})]:
 P=W/old;S=W/stage
 if S.exists():raise ValueError('fresh')
 S.mkdir();t=(P/'template.lean').read_text().replace(oldname,newname).replace(olddata,newdata).replace(oldproof,newproof)
 t=re.sub(r'\b(?:'+ '|'.join(m)+r')\b',lambda x:m[x.group()],t)
 (S/'template.lean').write_text(t);g=(P/'generate.py').read_text().replace(oldname,newname).replace('first registry','next registry');(S/'generate.py').write_text(g);(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
 (S/'instantiation01.json').write_text(json.dumps(dict(template_sha256=hashlib.sha256((P/'template.lean').read_bytes()).hexdigest(),template_path=str(P/'template.lean'),token_map=m,namespace_map=[oldname,newname],actual_data_api=[olddata,newdata],actual_constructor_api=[oldproof,newproof],source_scope='Exact symbolic theorem instantiation; actual check/position APIs inherited. No fresh capture/native credit.'),sort_keys=True)+'\n')
