from pathlib import Path
import json,hashlib
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-next-comparison115-transport-source01';A=W/'mac-asset-comparison110-transport-source02'
if S.exists():raise ValueError('immutable source')
S.mkdir()
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
old=W/'mac-registry-value-comparison102-source01/selected-data01.json';new=W/'mac-next-comparison115-data01/selected-data01.json';a=json.loads(old.read_bytes());b=json.loads(new.read_bytes())
def rename(x):return x+510 if 216<=x<471 else x+1016 if 32246<=x<32754 else x
def terms(v):return sorted([[rename(x),c]for x,c in v])
if len(a['entries'])!=len(b['entries']):raise ValueError('full source cardinality')
for o,n in zip(a['entries'],b['entries']):
 if n['bitColumn']!=rename(o['bitColumn'])or n['maximumBit']!=o['maximumBit']or n['before']!=terms(o['before'])or n['after']!=terms(o['after'])or n['pivot']!=rename(o['pivot'])or n['auxiliary']!=rename(o['auxiliary']):raise ValueError('every source entry transport')
 for ro,rn in zip(o['rows'],n['rows']):
  if rn['a']!=terms(ro['a'])or rn['b']!=terms(ro['b'])or rn['index']!=ro['index']+1016:raise ValueError('every actual row indexed transport')
t=(A/'rename-template.lean').read_text().replace('AssetComparison110','NextComparison115').replace('column+255','column+510').replace('column+508','column+1016');(S/'rename-template.lean').write_text(t)
g=(A/'generate.py').read_text().replace('AssetComparison110','NextComparison115').replace('start=10016+64*j','start=10524+64*j');line="emit('NextComparison115Numeric',(S/'numeric-template.lean').read_text(),['ShielddSecurity.NextComparison115.selected_numeric'])\n"
if g.count(line)!=1:raise ValueError('remove only qualified numeric repeat')
g=g.replace(line,'').replace('Selected-value numeric bridge and8 exact asset row transports only; final canonical assertion/shared constructor separate.','Nine nextValue exact row transport modules; selected_numeric is inherited from qualified110. Final canonical/assertion/shared constructor separate.')
(S/'generate.py').write_text(g);(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'source-binding01.json').write_text(json.dumps({'old':pin(old),'target':pin(new),'numeric_template':pin(W/'mac-value-comparison106-numeric-source03/template.lean'),'every_entry':254,'every_row':508,'scope':'DATA only; no new kernel credit.'},sort_keys=True)+'\n')
(S/'source-parser-refusal01.json').write_text('{"scope":"Earlier in-memory preparation script syntax if216/if32246 refused BEFOREany code executed; no source emission/kernel/intent/formal credit. Corrected maintained preparation stored."}\n')
