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
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);outputs=[]
for name in ['CapturedThreeCallGlobalBinding173D000', 'CapturedThreeCallGlobalBinding173D001', 'CapturedThreeCallGlobalBinding173D002', 'CapturedThreeCallGlobalBinding173D003', 'CapturedThreeCallGlobalBinding173D004', 'CapturedThreeCallGlobalBinding173D005', 'CapturedThreeCallGlobalBinding173D006', 'CapturedThreeCallGlobalBinding173D007', 'CapturedThreeCallGlobalBinding173D008', 'CapturedThreeCallGlobalBinding173D009', 'CapturedThreeCallGlobalBinding173D010', 'CapturedThreeCallGlobalBinding173D011', 'CapturedThreeCallGlobalBinding173D012', 'CapturedThreeCallGlobalBinding173D013', 'CapturedThreeCallGlobalBinding173D014', 'CapturedThreeCallGlobalBinding173D015', 'CapturedThreeCallGlobalBinding173D016', 'CapturedThreeCallGlobalBinding173D017', 'CapturedThreeCallGlobalBinding173D018', 'CapturedThreeCallGlobalBinding173D019', 'CapturedThreeCallGlobalBinding173D020', 'CapturedThreeCallGlobalBinding173D021', 'CapturedThreeCallGlobalBinding173D022', 'CapturedThreeCallGlobalBinding173D023', 'CapturedThreeCallGlobalBinding173D024', 'CapturedThreeCallGlobalBinding173D025', 'CapturedThreeCallGlobalBinding173D026', 'CapturedThreeCallGlobalBinding173D027', 'CapturedThreeCallGlobalBinding173D028', 'CapturedThreeCallGlobalBinding173D029', 'CapturedThreeCallGlobalBinding173D030', 'CapturedThreeCallGlobalBinding173D031', 'CapturedThreeCallGlobalBinding173D032', 'CapturedThreeCallGlobalBinding173D033', 'CapturedThreeCallGlobalBinding173D034', 'CapturedThreeCallGlobalBinding173D035', 'CapturedThreeCallGlobalBinding173D036', 'CapturedThreeCallGlobalBinding173D037', 'CapturedThreeCallGlobalBinding173D038', 'CapturedThreeCallGlobalBinding173D039', 'CapturedThreeCallGlobalBinding173D040', 'CapturedThreeCallGlobalBinding173D041', 'CapturedThreeCallGlobalBinding173D042', 'CapturedThreeCallGlobalBinding173D043', 'CapturedThreeCallGlobalBinding173D044', 'CapturedThreeCallGlobalBinding173D045', 'CapturedThreeCallGlobalBinding173D046', 'CapturedThreeCallGlobalBinding173D047', 'CapturedThreeCallGlobalBinding173D048', 'CapturedThreeCallGlobalBinding173']:
 t=(S/(name+'.template.lean')).read_text()
 names=['count','chunks','partition','copyCheck','copy_checked','arithmetic_sound','sound'] if name=='CapturedThreeCallGlobalBinding173' else ['rows','indices','productionCheck','checked','count','sound']
 audits=['ShielddSecurity.'+name+'.'+n for n in names]
 t+='\n'+''.join('set_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n'for n in audits)
 require(len(t.encode())<=262144,'finite source');p=r/(name+'.lean');p.write_text(t)
 outputs.append(dict(name=name,source=pin(p),audits=audits))
put('generation01.json',dict(outputs=outputs,generator=pin(Path(__file__)),templates={p.name:pin(p) for p in S.glob('*.template.lean')},scope='SOURCE-only exact ordered integer/copy packing coverage. Qualified pilot reused without replay; all new generated instances/root UNRUN. Finite captured-row equality derives each target only from full200770 indexed relation, no local/hash truth premise. Joined734..2305 plus ONE actualcopy200769 yields1573 selected positions. Shared constructor1467 unchanged; fullnative/legalTransfer OPEN.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(outputs=outputs,audits=sum(len(o['audits']) for o in outputs))))
