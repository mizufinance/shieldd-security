from pathlib import Path
import sys,json,hashlib,ast,runpy,os
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-full-arithmetic45-execution273';S=W/'mac-word-compatibility250-source01'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(p,v):
 with p.open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags')
require(not S.exists(),'immutable successor')
require(pin(P/'maintained/guard.py')['sha256']=='e1e43ace6927b7e3fe3904c69322be5fd6f62fcfe8839c5e75b97f418a394fa9','exact readonly configuration loader')
g=runpy.run_path(str(P/'maintained/guard.py'),run_name='SOURCE_CONFIGURATION_ONLY');c=g['read_config'](str(P/'config01.json'),pin(P/'config01.json')['sha256']);q=json.loads(Path(c['closure']['path']).read_bytes())['modules'];q.update(c['qualified_batch_imports'])
inputs={}
for n in ['SharedWordFlags220','SharedWordWitness221','CapturedWordRoot213','WordHints210',*['CapturedWordSlots211B'+str(i).zfill(3)for i in range(17)]]:
 v=q[n]['source'];require(pin(v['path'])==v,'exact accepted source '+n);inputs[v['path']]=v
body='''import ShielddSecurity.SharedWordFlags220
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.WordFlagCompatibility250
open WordHints210 SharedWordFlags220
def bitAt (n i : Nat) : Bool := decide (n/2^i%2=1)
theorem pair_offset (start width n : Nat) (pair : Nat × Bool)
 (member : pair∈(List.range' start width).zip (encodeBits width n)) :
 ∃ i<width,pair=(start+i,bitAt n i) := by
 induction width generalizing start n with
 | zero => simp only [List.range'_zero,encodeBits,List.zip_nil_left,List.not_mem_nil] at member
 | succ width ih =>
   simp only [List.range'_succ,encodeBits,List.zip_cons_cons,List.mem_cons] at member
   rcases member with same|tail
   · subst pair
     refine ⟨0,by omega,?_⟩
     simp only [Nat.add_zero,bitAt,Nat.pow_zero,Nat.div_one]
   · obtain ⟨i,bound,equal⟩:=ih (start+1) (n/2) tail
     refine ⟨i+1,by omega,equal.trans ?_⟩
     have bit : bitAt (n/2) i=bitAt n (i+1) := by
       simp only [bitAt,Nat.div_div_eq_div_mul,Nat.pow_succ,Nat.mul_comm]
     rw [bit]
     congr 1
     omega
def shape (a b : Slot) (exceptions : List (Nat × Nat)) : Bool := decide
 (a.start+a.width≤b.start ∨ b.start+b.width≤a.start ∨
  (a.start=b.start ∧ a.value=b.value) ∨
  (a.width=1 ∧ a.start=b.start ∧ (a.value,b.value)∈exceptions) ∨
  (b.width=1 ∧ a.start=b.start ∧ (b.value,a.value)∈exceptions))
def check (slots : List Slot) (exceptions : List (Nat × Nat)) : Bool :=
 slots.all (fun a => slots.all (fun b => shape a b exceptions))
def LowAgree (exceptions : List (Nat × Nat)) (numbers : Nat → Nat) : Prop :=
 ∀ pair∈exceptions,bitAt (numbers pair.1) 0=bitAt (numbers pair.2) 0
theorem offsets_agree (slots : List Slot) (exceptions : List (Nat × Nat))
 (numbers : Nat → Nat) (checked : check slots exceptions=true) (low : LowAgree exceptions numbers)
 (a : Slot) (knownA : a∈slots) (b : Slot) (knownB : b∈slots)
 (i j : Nat) (hi : i<a.width) (hj : j<b.width) (same : a.start+i=b.start+j) :
 bitAt (numbers a.value) i=bitAt (numbers b.value) j := by
 have cases:shape a b exceptions=true :=
   List.all_eq_true.mp (List.all_eq_true.mp checked a knownA) b knownB
 simp only [shape,decide_eq_true_eq] at cases
 rcases cases with disjoint|disjoint|⟨start,value⟩|⟨width,start,present⟩|⟨width,start,present⟩
 · omega
 · omega
 · have index:i=j := by omega
   rw [value,index]
 · have zeroI:i=0 := by omega
   have zeroJ:j=0 := by omega
   subst i;subst j
   exact low _ present
 · have zeroI:i=0 := by omega
   have zeroJ:j=0 := by omega
   subst i;subst j
   exact (low _ present).symm
theorem coherent (slots : List Slot) (exceptions : List (Nat × Nat))
 (numbers : Nat → Nat) (checked : check slots exceptions=true) (low : LowAgree exceptions numbers) :
 Coherent (assignments slots numbers) := by
 intro pair pairMember other otherMember same
 obtain ⟨a,knownA,pairMember⟩:=List.mem_flatMap.mp pairMember
 obtain ⟨b,knownB,otherMember⟩:=List.mem_flatMap.mp otherMember
 obtain ⟨i,hi,equal⟩:=pair_offset a.start a.width (numbers a.value) pair pairMember
 obtain ⟨j,hj,otherEqual⟩:=pair_offset b.start b.width (numbers b.value) other otherMember
 subst pair;subst other
 exact offsets_agree slots exceptions numbers checked low a knownA b knownB i j hi hj same
end ShielddSecurity.WordFlagCompatibility250
'''
actual='''import ShielddSecurity.WordFlagCompatibility250
import ShielddSecurity.SharedWordWitness221
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedWordCompatibility251
open WordFlagCompatibility250 SharedWordFlags220
def exceptions : List (Nat × Nat) := [(9059,9061),(10591,10593),(20935,20937)]
theorem checked : check SharedWordWitness221.wordSlots exceptions=true := by decide
theorem low_agree (numbers : Nat → Nat)
 (first : numbers 9059%2=numbers 9061%2)
 (second : numbers 10591%2=numbers 10593%2)
 (third : numbers 20935%2=numbers 20937%2) : LowAgree exceptions numbers := by
 intro pair member
 simp only [exceptions,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl <;>
   simp only [bitAt,Nat.pow_zero,Nat.div_one] <;>
   first | exact congrArg (fun x : Nat => decide (x=1)) first
         | exact congrArg (fun x : Nat => decide (x=1)) second
         | exact congrArg (fun x : Nat => decide (x=1)) third
theorem coherent (numbers : Nat → Nat)
 (first : numbers 9059%2=numbers 9061%2)
 (second : numbers 10591%2=numbers 10593%2)
 (third : numbers 20935%2=numbers 20937%2) :
 Coherent (assignments SharedWordWitness221.wordSlots numbers) :=
 WordFlagCompatibility250.coherent _ _ numbers checked (low_agree numbers first second third)
end ShielddSecurity.CapturedWordCompatibility251
'''
names={'WordFlagCompatibility250':['bitAt','pair_offset','shape','check','LowAgree','offsets_agree','coherent'],'CapturedWordCompatibility251':['exceptions','checked','low_agree','coherent']}
modules={n:dict(body=b,names=names[n])for n,b in [('WordFlagCompatibility250',body),('CapturedWordCompatibility251',actual)]}
require(os.statvfs(W).f_bavail*os.statvfs(W).f_frsize>=2*1024**3+4*1024**2,'fresh disk floor and source reserve')
S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-merkle-sparse243-source02/generate.py').read_bytes());ast.parse((S/'generate.py').read_bytes());put(S/'templates01.json',dict(modules=modules,inputs=inputs,scope=dict(status='SOURCE_ONLY_UNRUN',planned_modules=2,planned_reports=11,goal='Replace opaque66-window Coherent seed premise with actual compact interval-shape check and only three parity equalities; no semantic/row satisfaction premises',open=['All eleven audits remain UNRUN','Actual legal-input derivation of three parity bindings remains OPEN','Complete seed/all assertion truth/full Transfer remain OPEN'],runtime=c['runtime_sha'],source_context=c['canonical_context'])))
print(json.dumps(dict(stage=str(S),planned_modules=2,reports=11,inputs=len(inputs))))
