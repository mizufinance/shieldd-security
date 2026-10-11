from pathlib import Path
import json,hashlib,zlib,sys
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-canonical-comparisons216-source03';D=W/'mac-canonical-comparisons216-data01';P=52435875175126190479447740508185965837690552500527637822603658699938581184513
def req(ok,msg):
 if not ok:raise RuntimeError(msg)
def pin(p):
 b=Path(p).read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def strict(raw):
 def pairs(xs):
  d={}
  for k,v in xs:req(k not in d,'duplicate JSON');d[k]=v
  return d
 return json.loads(raw,object_pairs_hook=pairs)
def lc(terms,norm=False):
 return '['+','.join('('+str(c)+','+('-1'if norm else '((p:Int)-1)'if v==P-1 else str(v)) +')'if v==P-1 else '('+str(c)+','+str(v)+')'for c,v in terms)+']'
def row(r):return '⟨'+lc(r['a'])+','+lc(r['b'])+'⟩'
def append(names):
 return names[0] if len(names)==1 else names[0]+'++('+append(names[1:])+')'
req(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags');req(not S.exists(),'immutable source');qp=D/'qualification01.json';req(pin(qp)['sha256']=='2b71baa5cc20f31c5617f39d4a2e1affc482c4bff9381ec0a3180295e2719805','exact selected DATA');q=strict(qp.read_bytes());req(pin(q['data']['path'])==q['data'],'SHA before bounded decode');decoder=zlib.decompressobj();raw=decoder.decompress(Path(q['data']['path']).read_bytes(),8*1024**2+1);req(len(raw)==q['decoded_bytes']and len(raw)<=8*1024**2 and decoder.eof and not decoder.unused_data and not decoder.unconsumed_tail and hashlib.sha256(raw).hexdigest()==q['decoded_sha256'],'bounded EOF/trailing/size');data=strict(raw);inputs={str(qp):pin(qp),q['data']['path']:q['data']};modules={};prefix='''set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
'''
helper='''import ShielddSecurity.CompilerRowSlice63
import ShielddSecurity.ComparisonComposition103
'''+prefix+'''namespace ShielddSecurity.CanonicalComparisonSlices218
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ComparisonCertificate101
theorem slice (start count : Nat) (rows : List Row)
 (checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt start count rows=true)
 (bound : start+count≤177954) :
 ∀ row∈rows,∃ index<177954,CapturedFullArithmetic52.rowAt index=some row := by
 intro row member
 obtain ⟨index,found⟩:=List.mem_iff_getElem?.mp member
 obtain ⟨before,_⟩:=List.getElem?_eq_some_iff.mp found
 have length:rows.length=count := CompilerRowSlice63.count _ start count rows checked
 have ib:index<count := by omega
 refine ⟨start+index,by omega,?_⟩
 rw [CompilerRowSlice63.position _ start count rows checked index ib]
 exact found
theorem append (left right : List Entry)
 (a : ∀ row∈left.flatMap Entry.rows,∃ index<177954,CapturedFullArithmetic52.rowAt index=some row)
 (b : ∀ row∈right.flatMap Entry.rows,∃ index<177954,CapturedFullArithmetic52.rowAt index=some row) :
 ∀ row∈(left++right).flatMap Entry.rows,∃ index<177954,CapturedFullArithmetic52.rowAt index=some row := by
 intro row member
 rw [List.flatMap_append] at member
 rcases List.mem_append.mp member with member|member
 · exact a row member
 · exact b row member
end ShielddSecurity.CanonicalComparisonSlices218
''';modules['CanonicalComparisonSlices218']=dict(body=helper,names=['slice','append'])
for chain in data['chains']:
 if chain['slot']['start']==216:continue
 index=chain['word_index'];root='CapturedCanonical216W'+str(index).zfill(2);chunks=[chain['entries'][i:i+32]for i in range(0,254,32)];req(len(chunks)==8 and sum(map(len,chunks))==254,'eight finite chunks');chunknames=[];slot=chain['slot'];first=slot['start'];start=chain['row_start'];term=chain['terminal']
 for ci,entries in enumerate(chunks):
  name=root+'C'+str(ci).zfill(2);chunknames.append(name);initial=entries[0]['before'];output=entries[-1]['after'];rendered=[]
  for e in entries:rendered.append('⟨'+','.join([str(e['bitColumn']),str(e['maximumBit']).lower(),lc(e['before'],True),lc(e['after'],True),str(e['pivot']),str(e['auxiliary']),'['+','.join(row(r)for r in e['rows'])+']'])+'⟩')
  cs=start+64*ci;count=2*len(entries);body='import ShielddSecurity.CanonicalComparisonSlices218\n'+prefix+f'''namespace ShielddSecurity.{name}
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ComparisonCertificate101
def entries : List Entry := ['''+','.join(rendered)+f''']
def initial : Linear := {lc(initial,True)}
def actualRows : List Row := entries.flatMap Entry.rows
noncomputable def productionCheck : Bool := chainCheck initial entries
theorem production_checked : productionCheck=true := by decide +kernel
noncomputable def rowCheck : Bool := CompilerRowSlice63.check CapturedFullArithmetic52.rowAt {cs} {count} actualRows
theorem rows_checked : rowCheck=true := by decide +kernel
theorem output_exact : output initial entries={lc(output,True)} := by rfl
theorem selected : ∀ row∈entries.flatMap Entry.rows,∃ index<177954,CapturedFullArithmetic52.rowAt index=some row :=
 CanonicalComparisonSlices218.slice {cs} {count} actualRows rows_checked (by decide)
end ShielddSecurity.{name}
''';modules[name]=dict(body=body,names=['entries','initial','actualRows','productionCheck','production_checked','rowCheck','rows_checked','output_exact','selected'])
 wordModule='CapturedWordSlots211B'+str(index//4).zfill(3);ns='W'+str(index).zfill(2);aliases=['E'+str(i)for i in range(8)];body='import ShielddSecurity.CapturedCanonical217\nimport ShielddSecurity.'+wordModule+'\n'+''.join('import ShielddSecurity.'+n+'\n'for n in chunknames)+prefix+f'''namespace ShielddSecurity.{root}
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ComparisonCertificate101
abbrev Word := {wordModule}.{ns}.slot
'''+''.join('private abbrev '+aliases[i]+' := '+chunknames[i]+'.entries\n'for i in range(8))+f'''def entries : List Entry := {append(aliases)}
def initial : Linear := {chunknames[0]}.initial
def sourceOutput : Linear := {lc(term['raw_output'])}
def actualRows : List Row := entries.flatMap Entry.rows
noncomputable def productionCheck : Bool := chainCheck initial entries
theorem production_checked : productionCheck=true := by
 have h7:= {chunknames[7]}.production_checked
'''
 for i in range(6,-1,-1):body+=f''' have h{i} : chainCheck {chunknames[i]}.initial ({append(aliases[i:])})=true := by
  apply ComparisonComposition103.check_append
  · exact {chunknames[i]}.production_checked
  · rw [{chunknames[i]}.output_exact]
    exact h{i+1}
'''
 body+=' exact h0\n'+f'''theorem columns_checked : CanonicalWord215.columns {first} entries=WordHints210.columns Word := by decide
theorem initial_checked : canonical p initial=canonical p [(copy,1),({first},-1)] := by decide
theorem terminal_checked : CapturedFullAssertions54.recipeAt {term['position']}=some (true,.linear [(0,1)] sourceOutput) := by decide
theorem terminal_bound : {term['position']}<22816 := by decide
theorem output_port : canonical p sourceOutput=canonical p (unoutline copy (output initial entries)) := by decide +kernel
theorem selected : ∀ row∈entries.flatMap Entry.rows,∃ index<177954,CapturedFullArithmetic52.rowAt index=some row := by
'''
 for i in range(7):body+=' apply CanonicalComparisonSlices218.append\n · exact '+chunknames[i]+'.selected\n'
 body+=' exact '+chunknames[7]+'.selected\n'+f'''variable {{F : Type}} [Field F] [CharP F p]
theorem maximum (rho : Nat → F) : binary ((CanonicalWord215.pairs rho {first} entries).map Prod.snd)=p-1 := by
 change binary [false,'''+','.join(str(e['maximumBit']).lower()for e in chain['entries'])+''']=p-1
 decide +kernel
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) (one : rho 0=1) :
 ∃ n : Nat,n<p ∧ (n:F)=rho '''+str(slot['value'])+f''' :=
 CapturedCanonical217.sound rho satisfied one Word {first} {wordModule}.{ns}.first initial entries
  {wordModule}.{ns}.checked {wordModule}.{ns}.positions.1
  {wordModule}.{ns}.bits_checked {wordModule}.{ns}.positions.2 columns_checked initial_checked
  production_checked selected {term['position']} terminal_bound sourceOutput terminal_checked output_port (maximum rho)
end ShielddSecurity.{root}
''';modules[root]=dict(body=body,names=['Word','entries','initial','sourceOutput','actualRows','productionCheck','production_checked','columns_checked','initial_checked','terminal_checked','terminal_bound','output_port','selected','maximum','sound']);p=W/'mac-word-slots211-source01/source-root/ShielddSecurity'/(wordModule+'.lean');inputs[str(p)]=pin(p)
for p in[W/'mac-captured-canonical217-source02/source-root/ShielddSecurity/CapturedCanonical217.lean',W/'mac-indexed-row-slice63-source01/source-root/ShielddSecurity/CompilerRowSlice63.lean',W/'mac-comparison-composition103-source01/source-root/ShielddSecurity/ComparisonComposition103.lean']:inputs[str(p)]=pin(p)
req(len(modules)==118,'one generic/104 bounded chunks/13 roots');planned=sum(len(d['names'])for d in modules.values());S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-word-hints210-source03/generate.py').read_bytes());(S/'templates01.json').write_text(json.dumps(dict(modules=modules,inputs=inputs,scope='SOURCE_ONLY_UNRUN. Remaining13 actual canonical comparison chains, each8 finite32-entry chunks; reuse symbolic qualified103 composition and exact original row-slice checks. Full captured relation+rho0 derives13 canonical original-value representatives; no desired truth premise. First canonical word has separate216source02 using qualified105. All old216source01 UNRUN preserved.'),sort_keys=True,separators=(',',':'))+'\n');print(json.dumps(dict(stage=str(S),modules=len(modules),planned_audits=planned,body_bytes=sum(len(d['body'].encode())for d in modules.values()))))
