"""Independent literal actual-row and recipe parser for source06; no generator interpretation."""
from pathlib import Path
import hashlib,json,re,zlib
J=Path(__file__).resolve().parent;W=J.parent.parent;S=W/'mac-assertion-provider50-source06'
g=json.loads((S/'generation01.json').read_bytes());q=json.loads(Path(g['qualification']['path']).read_bytes())
coeffs=json.loads(Path(q['old_coefficients']['path']).read_bytes())['coefficients']+json.loads(Path(q['extra_coefficients']['path']).read_bytes())['coefficients']
def terms(text,constants):
 assert text.startswith('[') and text.endswith(']')
 inner=text[1:-1]
 if not inner:return []
 result=[];cursor=0
 for match in re.finditer(r'\((\d+),(c\d+|\d+)\)',inner):
  gap=inner[cursor:match.start()];assert gap==('' if cursor==0 else ',')
  value=constants[match[2]] if match[2].startswith('c') else int(match[2])
  result.append([int(match[1]),value]);cursor=match.end()
 assert cursor==len(inner)
 return result
checked_rows=checked_hints=0
for spec,block in zip(g['outputs'],q['chunks']):
 raw=Path(spec['source']['path']).read_bytes();text=raw.decode()
 assert hashlib.sha256(raw).hexdigest()==spec['source']['sha256']
 const={('c'+i):int(v)for i,v in re.findall(r'^private def c(\d+) : Int := (-?\d+)$',text,re.M)}
 actuals=[]
 for number,expression in re.findall(r'^private noncomputable def actual_c(\d+) : List Row := (\[.*\])$',text,re.M):
  assert int(number)==len(actuals)//4
  inner=expression[1:-1];cursor=0
  for match in re.finditer(r'⟨(\[.*?\]),(\[.*?\])⟩',inner):
   assert inner[cursor:match.start()]==('' if cursor==0 else ',')
   actuals.append([terms(match[1],const),terms(match[2],const)]);cursor=match.end()
  assert cursor==len(inner)
 hints=[]
 for number,expression in re.findall(r'^private noncomputable def hints_c(\d+) : List \(Bool × CompilerAssertionBlock51.Recipe\) := (\[.*\])$',text,re.M):
  assert int(number)==len(hints)//4
  inner=expression[1:-1];cursor=0
  for match in re.finditer(r'\((true|false),\.(linear|square) \(?(\[.*?\])\)? \(?(\[.*?\])\)?\)',inner):
   assert inner[cursor:match.start()]==('' if cursor==0 else ',')
   hints.append([match[1]=='true',match[2],terms(match[3],const),terms(match[4],const)]);cursor=match.end()
  assert cursor==len(inner)
 data=json.loads(zlib.decompress(Path(block['data']['path']).read_bytes()))
 assert len(actuals)==len(hints)==len(data['records'])==block['count']
 for actual,hint,record in zip(actuals,hints,data['records']):
  expected=[[[col,coeffs[co]]for col,co in vector]for vector in record['actual']]
  assert actual==expected
  if 'assertion' in record:
   kind='linear' if record['constructor']=='linear' else 'square'
   expected_hint=[True,kind,[[col,coeffs[co]]for col,co in record['x']],[[col,coeffs[co]]for col,co in record['y']]]
  else:
   left,right={200767:(1,22737),200768:(2,9),200769:(0,200692)}[record['index']]
   expected_hint=[False,'linear',[[left,1]],[[right,1]]]
  assert hint==expected_hint
  checked_rows+=1;checked_hints+=1
assert checked_rows==checked_hints==22816
report=dict(kind='INDEPENDENT_LITERAL_ROW_RECIPE_INTERPRETATION',source_stage=str(S),modules=90,actual_rows=checked_rows,recipes=checked_hints,method='Parse emitted literal actual/hint lists and private integer constants independently; compare each ordered column/coefficient pair and recipe to the separately reviewed original-row DATA.',parent_kernel_replay=False,legal_input_assertion_truth='OPEN',full_transfer='OPEN')
(J/'literal-source-row-review06.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))

