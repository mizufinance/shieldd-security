from pathlib import Path
import sys,json,hashlib,re
S=Path(__file__).resolve().parent;R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');D=R/'work/mac-merkle-family32-data01/selected-data01.json'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def lin(x):return '['+','.join(f'({c},{v})'for c,v in x)+']'
def write(p,b):
 if p.exists():require(p.read_bytes()==b,'immutable replay')
 else:
  with p.open('xb') as f:f.write(b)
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'flags')
require(pin(D)['sha256']=='54d0de34d64a281643185ec9e85f00cb4ad78e5f992680babd50dd9ed780a03f','data identity');d=json.loads(D.read_bytes());outputs={}
for i,level in enumerate(d['levels'][1:]):
 ns=f'MerkleFamily32SelectionL{i+2:02d}';xs=level['selection'];lo=level['low']-12;hi=level['low'];start=level['prefix_start']-12
 require(len(xs)==12 and [r['index']for r in xs]==list(range(start,start+12)),'positions');require(all(c!=0 for r in xs for c,v in r['a']+r['b']),'no native constant')
 t='''import ShielddSecurity.MerkleFamily32Selection
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.'''+ns+'''
open Compiler CompilerIndexed01 CompilerCompletion CompilerSegmentCompletion11
open CapturedInitial73419Generic01 (p copy)
'''
 t+='def actualRows : List Row := ['+','.join('⟨'+lin(r['a'])+','+lin(r['b'])+'⟩'for r in xs)+',TransferPoseidonCall04Shared01.rawCopy]\n'
 t+=f'def mapping : Array Nat := (List.range 13).toArray\ndef captureIndices := List.range\' {start} 12++[200769]\n'
 t+=f'''def productionCheck (candidate : List Row) (indices : Array Nat) : Bool :=
  checkOriginalCoverage p 0 candidate.toArray (MerkleFamily32Selection.actualRows {i}).toArray indices &&
  checkOriginalCoverage p 0 (MerkleFamily32Selection.actualRows {i}).toArray candidate.toArray indices
theorem checked : productionCheck actualRows mapping=true := by decide +kernel
theorem checked_parts : checkOriginalCoverage p 0 actualRows.toArray (MerkleFamily32Selection.actualRows {i}).toArray mapping=true ∧ checkOriginalCoverage p 0 (MerkleFamily32Selection.actualRows {i}).toArray actualRows.toArray mapping=true := by
  simpa only [productionCheck,Bool.and_eq_true] using checked
theorem counts : actualRows.length=13 ∧ captureIndices.length=13 := by decide +kernel
theorem support_checked : CapturedInitial73419Generic01.supportCheck {hi} actualRows=true := by decide +kernel
variable {{F : Type}} [Field F] [CharP F p]
theorem to_template (rho : Nat → F) (sat : Satisfies rho actualRows) : Satisfies rho (MerkleFamily32Selection.actualRows {i}) := by
  apply MerkleBits29.transfer rho (MerkleFamily32Selection.actualRows {i}) actualRows
  · have size := (MerkleFamily32Selection.counts {i}).2
    simpa only [mapping,size] using checked_parts.2
  · exact sat
theorem to_actual (rho : Nat → F) (sat : Satisfies rho (MerkleFamily32Selection.actualRows {i})) : Satisfies rho actualRows := by
  apply MerkleBits29.transfer rho actualRows (MerkleFamily32Selection.actualRows {i})
  · simpa only [counts.1,mapping] using checked_parts.1
  · exact sat
theorem complete (base : Nat → F) (linked : base copy=base 0) : Satisfies (run base (MerkleFamily32Selection.program {i})) actualRows :=
  to_actual _ (MerkleFamily32Selection.complete {i} base linked)
def segment : Segment F copy :=
  CapturedInitial73419Generic01.makeSegment (MerkleFamily32Selection.program {i}) actualRows {lo} {hi}
    (List.all_eq_true.mp MerkleFamily32Selection.writes_checked {i} (List.mem_finRange {i})) support_checked complete
'''
 # Explicit scope: exact original bodies plus one actual shared-copy row, not all-parent inclusion.
 if i==0:
  t+='''def badCoefficient : List Row := let first := actualRows.headD ⟨[],[]⟩; ⟨first.a.map (fun term => if term.1=139 then (term.1,term.2+1) else term),first.b⟩::actualRows.tail
def badCopy : List Row := actualRows.take 12++[⟨[],[(copy,2),(0,-1)]⟩]
theorem coefficient_rejected : productionCheck badCoefficient mapping=false := by decide +kernel
theorem index_rejected : productionCheck actualRows (mapping.set! 0 1)=false := by decide +kernel
theorem omission_rejected : productionCheck (actualRows.take 12) mapping=false := by decide +kernel
theorem copy_rejected : productionCheck badCopy mapping=false := by decide +kernel
'''
 t+=f'end ShielddSecurity.{ns}\n';names=re.findall(r'^\s*(?:def|theorem) (\w+)',t,re.M)
 t+='\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.{ns}.{n}\n#print axioms ShielddSecurity.{ns}.{n}\n'for n in names)
 b=t.encode();require(len(b)<=262144,'source cap');write(S/'source-root/ShielddSecurity'/(ns+'.lean'),b);outputs[ns]=pin(S/'source-root/ShielddSecurity'/(ns+'.lean'))
write(S/'generation01.json',(json.dumps(dict(data=pin(D),generator=pin(Path(__file__)),sources=outputs),sort_keys=True)+'\n').encode());print(len(outputs),sum(x['bytes']for x in outputs.values()))
