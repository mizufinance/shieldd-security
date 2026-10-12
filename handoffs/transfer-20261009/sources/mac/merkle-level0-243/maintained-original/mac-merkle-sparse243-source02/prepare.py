from pathlib import Path
import json,hashlib,sys,re,os
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-merkle-sparse243-source02';A=W/'mac-full-arithmetic45-source01';P=W/'mac-merkle-middle239-source01';Q=W/'mac-merkle-global240-source01'
def require(c,m):
 if not c:raise RuntimeError(m)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated source preparation');require(not S.exists(),'immutable fresh source')
pv=json.loads((P/'templates01.json').read_bytes());qv=json.loads((Q/'templates01.json').read_bytes());require(pin(P/'templates01.json')==json.loads((P/'producer-manifest01.json').read_bytes())['templates01.json'],'exact local template');require(pin(Q/'templates01.json')==json.loads((Q/'producer-manifest01.json').read_bytes())['templates01.json'],'exact symbolic global template')
local=pv['modules']['CapturedMerkleMiddle239Local']['body'];globalbody=qv['modules']['CapturedMerkleGlobalArithmetic184L01B21']['body'];require('drop 284' in local and 'drop 336' in globalbody,'literal predecessor slice')
qualification=json.loads((A/'qualification01.json').read_bytes());generation=json.loads((A/'generation01.json').read_bytes());require(len(qualification['chunks'])==599 and len(generation['outputs'])==599,'exact arithmetic leaf census')
inputs={str(P/'templates01.json'):pin(P/'templates01.json'),str(Q/'templates01.json'):pin(Q/'templates01.json'),str(A/'qualification01.json'):pin(A/'qualification01.json'),str(A/'generation01.json'):pin(A/'generation01.json')};sources={};mods={};positions=[];data=[]
def actual(position):
 chunk=next(c for c in qualification['chunks']if c['start']<=position<c['start']+c['count']);index=chunk['index'];module='CapturedArithmetic45B'+str(index).zfill(4);record=generation['outputs'][index];require(record['name']==module,'source manifest index')
 if index not in sources:
  p=Path(record['source']['path']);require(pin(p)==record['source'],'qualified literal source input');text=p.read_text();part=text.split('noncomputable def actual : List Row := ',1)[1].split('\ntheorem span_exact',1)[0];rows=re.findall('⟨([^⟨⟩]*)⟩',part);require(len(rows)==chunk['count'],'exact ordered literal row census');sources[index]=rows;inputs[str(p)]=record['source']
 return module,sources[index][position-chunk['start']]
for level in range(0,15):
 for block in range(4,27):
  if level==1 and block in [20,21,22,23]:continue
  offset=16*block;count=min(16,424-offset);start=3146+424*level+offset;drop=offset-52;name=f'CapturedMerkleSparse243L{level:02d}B{block:02d}';globalname=f'CapturedMerkleGlobalArithmetic184L{level:02d}B{block:02d}';branches=[];imports=[]
  for position in range(start,start+count):
   module,row=actual(position);imports.append(module);r=row.replace('linear ArithmeticCoefficients39.value (inputs ','CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value ('+module+'.inputs ');branches.append(' | '+str(position)+' => some ⟨'+r+'⟩');positions.append(position)
  b=local.replace('CapturedMerkleMiddle239Local',name).replace('import ShielddSecurity.CapturedArithmetic45B0018\n',''.join('import ShielddSecurity.'+n+'\n'for n in dict.fromkeys(imports))).replace('drop 284','drop '+str(drop)).replace('take 16','take '+str(count)).replace('396 1272','396 '+str(424*(level+2))).replace("List.range' 3906 16",f"List.range' {start} {count}").replace('rows.length=16','rows.length='+str(count))
  a=b.index('def localParent :');z=b.index('\ndef localCheck',a);b=b[:a]+'def localParent : Nat → Option Row\n'+'\n'.join(branches)+'\n | _ => none'+b[z:];mods[name]={'body':b,'names':['rows','indices','localParent','localCheck','local_checked','count']}
  g=globalbody.replace('CapturedMerkleMiddle239Local',name).replace('CapturedMerkleGlobalArithmetic184L01B21',globalname).replace('arithmeticRows 1','arithmeticRows '+str(level)).replace('drop 336','drop '+str(offset)).replace('take 16','take '+str(count)).replace('rows.length=16','rows.length='+str(count))
  a=g.index(' change position ∈ [');z=g.index('\n all_goals rfl',a);g=g[:a]+' change position ∈ ['+','.join(map(str,range(start,start+count)))+'] at member\n simp only [List.mem_cons,List.not_mem_nil,or_false] at member\n rcases member with '+'|'.join(['rfl']*count)+g[z:];mods[globalname]={'body':g,'names':['rows','rows_exact','indices','localParent','parent_equal','productionCheck','checked','count','sound']};data.append(dict(level=level,block=block,start=start,count=count,template_drop=drop,outer_swap_offset=424*(level+2),local=name,global_module=globalname,arithmetic_sources=list(dict.fromkeys(imports))))
require(len(mods)==682 and len(positions)==5336 and len(positions)==len(set(positions)),'exact new unqualified tail position count');allbytes=sum(len(v['body'].encode())for v in mods.values());require(allbytes<4*1024**2 and all(len(v['body'].encode())<262144 for v in mods.values()),'finite source budget');require(os.statvfs(W).f_bavail*os.statvfs(W).f_frsize>2*1024**3+16*1024**2,'disk reserve')
inputs[str(W/'mac-merkle-sparse243-source01/producer-manifest01.json')]=pin(W/'mac-merkle-sparse243-source01/producer-manifest01.json')
# Correct SOURCE topology to actual Fin15 levels0..14, retaining source01 as UNRUN history. No active267 source changes. Other636 selected files byte-identical; level15 unused proposal replaced by actual missing level0.
# Link exact direct dependencies via preserved source-qualified template inputs; guard qualifies full imports before each job.
for v in [pv,qv]:
 for p,v in v['inputs'].items():
  require(pin(p)==v,'exact preserved template dependency');inputs[p]=v
S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((P/'generate.py').read_bytes());(S/'templates01.json').write_text(json.dumps(dict(modules=mods,inputs=inputs,scope='SOURCE_ONLY_UNRUN 341 sparse local certificates and341 symbolic global wrappers. 5336 distinct actual Merkle tail positions on levels0..14; inactive15 entries in source01 are historical UNRUN proposal only. Exact template slice before two injective column maps; sparse literal qualified arithmetic-parent branches; global equality proves position-specific full rowAt agreement before transferring finite check. Full relation remains legitimate soundness antecedent; no target row/hash truth premise. Already qualified64 positions never rebuilt. Runtime context and current inputs remain preserved.'),sort_keys=True,separators=(',',':'))+'\n');(S/'position-map01.json').write_text(json.dumps(dict(chunks=data,unique_positions=len(positions),planned_audits=341*15,source_body_bytes=allbytes),sort_keys=True,separators=(',',':'))+'\n');print(json.dumps(dict(stage=str(S),modules=len(mods),positions=len(positions),source_body_bytes=allbytes,input_sources=len(inputs))))
