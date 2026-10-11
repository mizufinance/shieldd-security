"""Unchanged isolated generation and independent local coefficient interpretation."""
import ast,hashlib,json,re,shutil,subprocess,zlib
from pathlib import Path
D=Path(__file__).resolve().parent;W=D.parent.parent
S=W/'mac-assertion-provider50-source04';OUT=D/'source-regeneration04'
OUT.mkdir(exist_ok=False);shutil.copyfile(S/'generate.py',OUT/'generate.py')
subprocess.run(['python3','-I','-B','-S',str(OUT/'generate.py')],check=True)
g=json.loads((S/'generation01.json').read_bytes());q=json.loads(Path(g['qualification']['path']).read_bytes())
orig=Path(q['old_coefficients']['path']);extra=Path(q['extra_coefficients']['path'])
coefficients=json.loads(orig.read_bytes())['coefficients']+json.loads(extra.read_bytes())['coefficients']
module=ast.parse((D/'check_extra_coefficients.py').read_text())
functions=[x for x in module.body if isinstance(x,ast.FunctionDef) and x.name in ['parse','lookup']]
ns={'re':re};exec(compile(ast.Module(body=functions,type_ignores=[]),'independent-lookup','exec'),ns)
total=0
for emitted,chunk in zip(g['outputs'],q['chunks']):
 src=Path(emitted['source']['path']);raw=src.read_bytes();fresh=OUT/'source-root/ShielddSecurity'/src.name
 assert fresh.read_bytes()==raw
 assert len(raw)==emitted['source']['bytes'] and hashlib.sha256(raw).hexdigest()==emitted['source']['sha256']
 decoded=zlib.decompress(Path(chunk['data']['path']).read_bytes());data=json.loads(decoded)
 used=sorted({c for item in data['records'] for vec in [*item['actual'],item.get('x',[]),item.get('y',[])] for _,c in vec})
 assert used==emitted['local_coefficient_ids'] and len(used)==emitted['local_coefficient_count']<=266
 match=re.search(r'^private noncomputable def localCoefficient \(index : Nat\) : Int := (.*)$',raw.decode(),re.M);assert match
 tree=ns['parse'](match[1]);assert [ns['lookup'](tree,i) for i in range(len(used))]==[coefficients[i] for i in used]
 assert ns['lookup'](tree,len(used))==coefficients[used[-1]]
 names=re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)',raw.decode(),re.M)
 assert len(names)==9 and emitted['audits']==['ShielddSecurity.'+emitted['name']+'.'+n for n in names]
 total+=len(raw)
assert len(g['outputs'])==90
report=dict(kind='SOURCE_GENERATION_AND_LOCAL_COEFFICIENT_REVIEW',generator_sha256=hashlib.sha256((S/'generate.py').read_bytes()).hexdigest(),
qualification=q['chunks'][0]['data'],modules=90,public_declarations=810,source_bytes=total,max_local_coefficients=266,
method='Unchanged isolated generator reproduces every source byte; independent lexical lookup-tree parser checks every coefficient literal against previously reviewed immutable original-row DATA.',
kernel_replay=False,full_transfer='OPEN')
(D/'source-regeneration-review04.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))

