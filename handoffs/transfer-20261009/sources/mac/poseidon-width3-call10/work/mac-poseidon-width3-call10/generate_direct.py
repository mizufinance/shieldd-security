"""First width3 folded/full/partial pilots: actual consumers plus complete row construction."""
import hashlib,json,os,re,sys
if not __debug__: raise RuntimeError("Optimized Python unsupported")
from pathlib import Path
from validate_records import validate_node
S=Path(__file__).resolve().parent;R=S.parents[1];O=R/'outputs/mac-poseidon-width3-call10';P=S/'project/ShielddSecurity'
EXPECTED_DESCRIPTOR_SHA='01b68f32bf6896a6122805713cdd5448105d2aab2da056699c9d35dd57f162ff'
sha=lambda b:hashlib.sha256(b).hexdigest();raw=(O/'rounds02.json').read_bytes()
assert sha(raw)==EXPECTED_DESCRIPTOR_SHA
d=json.loads(raw);assert d['parameter_sha256']=='f45040142a56e16bb8480f1f6648621d32f456646cfaf77beca2b05a6bb12742'
assert d['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
parameter_path=R/'work/runtime-snapshot/crates/crypto/primitives/params/poseidon381.json'
parameter_bytes=parameter_path.read_bytes()
assert sha(parameter_bytes)==d['parameter_sha256']
assert json.loads(parameter_bytes)==d['parameters']
files=[]
def save(module,lines):
 b=('\n'.join(lines)+'\n').encode();p=P/(module+'.lean')
 if p.exists() and p.read_bytes()!=b:
  hist=O/'source-history';hist.mkdir(exist_ok=True);old=p.read_bytes();(hist/(module+'-'+sha(old)+'.lean')).write_bytes(old)
 tmp=p.with_suffix('.tmp');tmp.write_bytes(b);os.replace(tmp,p);files.append(dict(module=module,sha256=sha(b),bytes=len(b)))
def audit(module,name):return ['set_option pp.all true in',f'#check @ShielddSecurity.{module}.{name}',f'#print axioms ShielddSecurity.{module}.{name}']
def theorem(lines,module,name,body):lines.extend(['theorem '+name+' : '+body]+audit(module,name))
params=d['parameters'];assert len(params['ark'])==65 and len(params['mds'])==3
rows={r['capture_index']:r for r in d['indexed_original_rows']}
for scope in d['selected_rounds']:
 index=scope['round'];assert index in [0,1]
 if sys.argv[1:]==['--probe'] and index!=0:continue
 stem=f'TransferPoseidonWidth3Prefix10R{index:02d}';nodes={n['source_node']:n for n in scope['nodes']};cuts={n['source_node']:n for n in scope['external_ports']};constants={c['source_constant']:c['integer'] for c in scope['constants']};pool={}
 def lc(terms):
  key=tuple(map(tuple,terms))
  if key not in pool:pool[key]='lc'+str(len(pool))
  return pool[key]
 def terms(ref):
  kind,value=ref
  if kind=='native':return [[0,value]] if value else []
  if kind==0:return [[0,constants[value]]] if constants[value] else []
  assert kind==2
  return nodes[value]['expression']['terms'] if value in nodes else cuts[value]['expression']['terms']
 steps=[];writes=[]
 for node in scope['nodes']:
  validate_node(node);cert=node['certificate'];ctor=cert['constructor']
  if ctor in ['foldedLeft','foldedRight']:
   port=node['left'] if ctor=='foldedLeft' else node['right'];assert port[0]==0 and cert['coefficient']==constants[port[1]]
  if ctor not in ['square','product']:continue
  z=node['expression']['terms'];assert len(z)==1 and z[0][1]==1;out=z[0][0];writes.append(out)
  x=lc(terms(node['left']));y=lc(terms(node['right']))
  if ctor=='square':assert node['left']==node['right'];steps.append(f'.square {x} [] {out}')
  else:
   aux=cert['auxiliary'];assert len(aux)==1 and aux[0][1]==1 and aux[0][0]!=out;writes.append(aux[0][0]);steps.append(f'.product {x} {y} [] {out} {aux[0][0]}')
 assert len(steps)==sum(n['certificate']['constructor'] in ['square','product'] for n in scope['nodes']);low,high=min(writes),max(writes);assert low>=22738
 phases={name:[lc(terms(ref)) for ref in scope['phase_ports'][key]] for name,key in [('before','before'),('shifted','after_ark'),('transformed','after_sbox'),('after','after_mds')]}
 indices=scope['rows_with_actual_copy_link'];assert indices[-1]==d['actual_copy_row_index'];count=len(indices);mapping={r:i for i,r in enumerate(indices)};hints=[]
 for column,ref in enumerate(scope['phase_ports']['after_sbox']):
  if not(index<4 or index>=61 or column==0):hints.append('.constant 0');continue
  if ref[0]=='native':
   assert index==0 and column in [0,2] and scope['phase_ports']['after_ark'][column][0]=='native'
   coefficient=scope['phase_ports']['after_ark'][column][1];assert pow(coefficient,5,int(d['modulus']))==ref[1];hints.append('.constant '+str(coefficient));continue
  product=nodes[ref[1]];cert=product['certificate'];assert cert['constructor']=='product' and product['right']==scope['phase_ports']['after_ark'][column]
  fourth=nodes[product['left'][1]];square=nodes[fourth['left'][1]]
  assert fourth['certificate']['constructor']=='square' and fourth['left']==fourth['right']
  assert square['certificate']['constructor']=='square' and square['left']==square['right']==scope['phase_ports']['after_ark'][column]
  hints.append('.arithmetic ⟨'+', '.join([lc(square['expression']['terms']),lc(fourth['expression']['terms']),lc(cert['auxiliary'])]+list(map(str,[mapping[square['certificate']['rows'][0]],mapping[fourth['certificate']['rows'][0]],mapping[cert['rows'][0]],mapping[cert['rows'][1]]])))+'⟩')
 rowDefs=[f'def row{i} : Row := ⟨{lc(rows[r]["a"])},{lc(rows[r]["b"])}⟩' for i,r in enumerate(indices)]
 lines=['-- GENERATED by generate_direct.py; edit generator.','import ShielddSecurity.PoseidonIndexedFolded02','import ShielddSecurity.CompilerOrder','import ShielddSecurity.CompilerPriorFrame01','import ShielddSecurity.TransferPoseidonWidth3Parameters08','set_option maxHeartbeats 900000','set_option maxRecDepth 8192',f'namespace ShielddSecurity.{stem}','open Compiler CompilerIndexed01 CompilerCompletion Poseidon PoseidonIndexedFolded02',f'def p : Nat := {d["modulus"]}',f'def copy : Nat := {d["constant_copy"]}','def parameters : Parameters Int 3 := TransferPoseidonWidth3Parameters08.parameters']
 lines += [f'def {name} : Linear := ['+', '.join(f'({column},{coefficient})' for column,coefficient in body)+']' for body,name in pool.items()]
 for name,refs in phases.items():lines += [f'def {name} (column : Fin 3) : Linear := match column.val with']+[f'  | {i} => {ref}' for i,ref in enumerate(refs)]+['  | _ => []']
 lines += rowDefs+['def originalRows : Array Row := Array.mk ['+', '.join(f'row{i}' for i in range(count))+']','def captureIndices : Array Nat := Array.mk ['+', '.join(map(str,indices))+']','def fifthHints (column : Fin 3) : FifthHint := match column.val with']+[f'  | {i} => {hint}' for i,hint in enumerate(hints)]+['  | _ => .constant 0','def materializedSteps : List Step := [\n  '+',\n  '.join(steps)+']','def copyStep : Step := .equal [(0,1)] [(0,1)]','def steps : List Step := materializedSteps++[copyStep]','def emittedRows : Array Row := (emitted steps).toArray',f'def rowMapping : Array Nat := (List.range {count}).toArray','def cutTerms (state : State Linear 3) (input : Nat) : Linear := if bound : input<3 then state ⟨input,bound⟩ else []','def productionCheck (candidateRows : Array Row) (candidateParameters : Parameters Int 3)','    (candidateBefore candidateAfter : State Linear 3) (candidateHints : Fin 3 → FifthHint) (mapping : Array Nat) : Bool :=',f'  checkRowAt p candidateRows {count-1} ⟨[(0,1),(copy,-1)],[]⟩ &&',f'  checkRound p copy candidateRows candidateParameters {index} candidateBefore shifted transformed candidateAfter candidateHints &&','  checkOriginalCoverage p copy candidateRows emittedRows mapping &&','  CompilerPriorFrame01.checkSupport 3 (cutTerms candidateBefore) steps',f'end ShielddSecurity.{stem}']
 save(stem+'Data01',lines)
 if sys.argv[1:]==['--probe']:continue
 def header(module):return ['-- GENERATED by generate_direct.py; edit generator.',f'import ShielddSecurity.{stem}Data01','set_option maxHeartbeats 900000','set_option maxRecDepth 8192',f'namespace ShielddSecurity.{module}',f'open Compiler CompilerIndexed01 CompilerCompletion Poseidon PoseidonIndexedFolded02 {stem}']
 module=stem+'ConsumerChecks01';lines=header(module)
 if index==0:lines.insert(2,'import ShielddSecurity.TransferPoseidonWidth3Prefix10AbsorbProbe01')
 for col in range(3):theorem(lines,module,f'column{col}_checked',f'checkColumn p copy originalRows parameters {index} before shifted transformed fifthHints {col}=true := '+(f'TransferPoseidonWidth3Prefix10AbsorbProbe01.column{col}_checked' if index==0 else 'by decide +kernel'))
 for row in range(3):theorem(lines,module,f'mix{row}_checked',f'canonical p (after {row})=canonical p (mixLinear parameters.mds transformed {row}) := '+(f'TransferPoseidonWidth3Prefix10AbsorbProbe01.mix{row}_checked' if index==0 else 'by decide +kernel'))
 lines += [f'end ShielddSecurity.{module}'];save(module,lines)
 module=stem+'CoverageChecks01';lines=header(module)
 for i in range(count):theorem(lines,module,f'row{i}_checked',f'checkOriginalAt p copy originalRows emittedRows rowMapping {i}=true := by decide +kernel')
 lines += [f'end ShielddSecurity.{module}'];save(module,lines)
 module=stem+'ProgramChecks01';lines=header(module)
 for name,body in [('actual_copy_checked',f'checkRowAt p originalRows {count-1} ⟨[(0,1),(copy,-1)],[]⟩=true'),('ordered_checked','CompilerOrder.checkOrder [0,copy] [] steps=true'),('writes_checked',f'(PoseidonCompletion.writes steps).all (fun column => decide ({low}≤column ∧ column≤{high}))=true'),('cut_support_checked','CompilerPriorFrame01.checkSupport 3 (cutTerms before) steps=true'),('raw_support_checked',f'originalRows.toList.all (fun row => (row.a++row.b).all (fun term => decide (term.1≤{high} ∨ term.1=copy)))=true'),('rows_shape',f'originalRows.size={count} ∧ materializedSteps.length={len(steps)} ∧ steps.length={len(steps)+1} ∧ captureIndices.toList=List.range\' {indices[0]} {count-1}++[200769]')]:theorem(lines,module,name,body+' := by decide +kernel')
 lines += [f'end ShielddSecurity.{module}'];save(module,lines)
 template=(S/'direct-proof-template.lean.txt').read_text().replace('TransferPoseidonLate03',stem).replace('PoseidonIndexedRound01','PoseidonIndexedFolded02')
 for token in ['Fin','Int','Linear','checkSupport','completed_inputs']:template=re.sub(r'\b'+token+r' 6\b',token+' 3',template)
 for placeholder,value,expected in [('@ROUND@',index,10),('@COPY_ROW@',count-1,2),('@WRITE_LOW@',low,1),('@WRITE_HIGH@',high,2)]:
  assert template.count(placeholder)==expected,(placeholder,template.count(placeholder))
  template=template.replace(placeholder,str(value))
 template=template.replace('column=0 ∨ column=1 ∨ column=2 ∨ column=3 ∨ column=4 ∨ column=5','column=0 ∨ column=1 ∨ column=2').replace('rfl|rfl|rfl|rfl|rfl|rfl','rfl|rfl|rfl').replace('    · exact column3_checked\n    · exact column4_checked\n    · exact column5_checked\n','').replace('    · exact mix3_checked\n    · exact mix4_checked\n    · exact mix5_checked\n','')
 template=template.replace('@ROWCASES@',' ∨ '.join(f'index={i}' for i in range(count))).replace('@ROWPATTERNS@','|'.join('rfl' for _ in range(count))).replace('@ROWPROOFS@','\n'.join(f'    · exact row{i}_checked' for i in range(count)))
 module=stem+'Proof01';names=re.findall(r'^theorem (\w+)',template,re.M)
 # Full signatures are appended, leaving doc comments adjacent to declarations.
 template+='\n'+'\n'.join('\n'.join(audit(module,name)) for name in names)+'\n';save(module,template.rstrip().splitlines())
assert (O/'rounds02.json').read_bytes()==raw
attempt=1
while (O/f'direct-generation{attempt:02d}.json').exists():attempt+=1
target=O/f'direct-generation{attempt:02d}.json';target.write_text(json.dumps(dict(generator_sha256=sha(Path(__file__).read_bytes()),descriptor_sha256=sha(raw),template_sha256=sha((S/'direct-proof-template.lean.txt').read_bytes()),validator_sha256=sha((S/'validate_records.py').read_bytes()),exporter_sha256=sha((S/'export_rounds.py').read_bytes()),parameter_path=str(parameter_path.relative_to(R)),parameter_sha256=sha(parameter_bytes),runtime_sha=d['runtime_sha'],sources=files,width=3,rounds=[0] if sys.argv[1:]==['--probe'] else [0,1],native_state0_and2_folded=True,cut_context='prior LC values; upstream closure OPEN'),indent=2)+'\n')
print(json.dumps(dict(modules=len(files),bytes=sum(x['bytes'] for x in files))))
