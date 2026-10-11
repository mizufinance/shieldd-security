from pathlib import Path
import sys,json,hashlib,re
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=Path(__file__).resolve().parent
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags')
require(not(S/'producer-manifest01.json').exists()and not(S/'source-root').exists(),'immutable new emission')
data=W/'mac-registry-value-comparison102-source01/selected-data01.json';b=data.read_bytes();require(len(b)==172696 and hashlib.sha256(b).hexdigest()=='5789daa5244dd0fd0fd12d4180e45821ccc7632481b628499fcc9fa86f48b77d','exact source DATA before decode');d=json.loads(b)
template=W/'mac-registry-value-comparison102-source02/template.lean';b=template.read_bytes();require(hashlib.sha256(b).hexdigest()=='7bba5a35da8423f70e78928366011fee22db1db2ca2e9cb8e9f3b96f870b8314','exact repaired template before decode');templateText=b.decode()
P=52435875175126190479447740508185965837690552500527637822603658699938581184513
def coeff(v,signed=False):
 if v>P//2:return str(v-P)if signed else'((p:Int)'+str(v-P)+')'
 return str(v)
def lc(a,signed=False):return '['+','.join('('+str(x)+','+coeff(v,signed)+')'for x,v in a)+']'
def row(r):return '⟨'+lc(r['a'])+','+lc(r['b'])+'⟩'
def entry(e):return '⟨'+','.join([str(e['bitColumn']),str(e['maximumBit']).lower(),lc(e['before'],True),lc(e['after'],True),str(e['pivot']),str(e['auxiliary']),'['+','.join(row(r)for r in e['rows'])+']'])+'⟩'
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);outputs=[]
for chunk in range(1,8):
 start=chunk*32;part=d['entries'][start:min(start+32,254)];require(0<len(part)<=32,'bounded chunk');name=f'CapturedValueComparison104C{chunk:02d}'
 t=templateText.replace('CapturedValueComparison102Pilot',name).replace('9508 64',f'{9508+2*start} {2*len(part)}').replace('@ENTRIES@','['+','.join(entry(e)for e in part)+']').replace('@INITIAL@',lc(part[0]['before'],True)).replace('@OUTPUT@',lc(part[-1]['after'],True));require('@'not in t,'all placeholders')
 names=re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)',t,re.M);require(len(names)==len(set(names))==9,'declaration inventory')
 audits=['ShielddSecurity.'+name+'.'+n for n in names];t+='\n'+''.join('set_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n'for n in audits)
 p=r/(name+'.lean');require(len(t.encode())<=262144,'finite source');p.write_text(t)
 outputs.append(dict(name=name,source=pin(p),audits=audits,start=9508+2*start,length=2*len(part),entry_start=start,entry_count=len(part)))
put('generation01.json',dict(outputs=outputs,data=pin(data),template=pin(template),generator=pin(Path(__file__)),inherited_first32='CapturedValueComparison102Pilot source02 qualified attempt836',scope='Seven disjoint remaining product slices, scope checker equality and arithmetic satisfaction implication; no legal canonical comparison conclusion. 254 entries total with inherited first32; exact508 arithmetic positions9508..10015.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(outputs=len(outputs),source_bytes=sum(v['source']['bytes']for v in outputs))))
