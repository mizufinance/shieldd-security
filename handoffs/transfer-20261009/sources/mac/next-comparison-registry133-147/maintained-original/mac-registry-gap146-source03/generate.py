from pathlib import Path
import sys,json,hashlib
S=Path(__file__).resolve().parent
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags')
require(not(S/'producer-manifest01.json').exists()and not(S/'source-root').exists(),'immutable emission')
d=S.parent/'mac-registry-gap145-data01/selected-data01.json';require(pin(d)['sha256']=='ce453ccc4a8459dbbe645b9bd6377744fe981e99918b3f9d7aa30e377505af44','frozen actual-row DATA')
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);t=(S/'template.lean').read_text();audits=['ShielddSecurity.CapturedRegistryGap146.'+n for n in ['completed', 'first_high', 'first_equal', 'first_low', 'second_high', 'second_equal', 'second_low', 'regulated_frame', 'gap_zero', 'actualRows', 'normalizedRows', 'positionCheck', 'position_checked', 'actual_position', 'reverseCheck', 'reverse_checked', 'complete']]
t+='\n'+''.join('set_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n'for n in audits);require(len(t.encode())<=262144,'finite source');p=r/'CapturedRegistryGap146.lean';p.write_text(t)
put('generation01.json',dict(outputs=[dict(name='CapturedRegistryGap146',source=pin(p),audits=audits)],generator=pin(Path(__file__)),data=pin(d),template=pin(S/'template.lean'),scope='Same completed assignment derives assertion179421 from RegistrySem, captured arithmetic and independently seeded lexicographic hints. No desired hash/order/assertion truth premise; anchor178117 and later obligations OPEN.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(source=pin(p),audits=len(audits))))
