from pathlib import Path
import sys,json,hashlib
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-word-root213-source02'
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated SOURCE flags');require(not S.exists(),'immutable SOURCE')
g=json.loads((W/'mac-word-slots211-source01/generation01.json').read_bytes());data=json.loads((W/'mac-word-slots211-source01/selected-data01.json').read_bytes());require(len(data['selected'])==66,'exact finite word family')
names=[o['name']for o in g['outputs']]
heads=[names[i//4]+'.W'+str(i).zfill(2)for i in range(66)]
literal='['+','.join('('+h+'.slot,'+h+'.first)'for h in heads)+']'
def conjunction(xs):
 require(bool(xs),'nonempty conjunction')
 return '⟨'+xs[0]+',by intro entry member;cases member⟩'if len(xs)==1 else '⟨'+xs[0]+','+conjunction(xs[1:])+'⟩'
body=''.join('import ShielddSecurity.'+n+'\n'for n in names)+'''import ShielddSecurity.SharedWordSeed212
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedWordRoot213
open WordHints210 CompilerAssertionBlock51 CompilerArithmeticTransport41
'''+f'def words : List (Slot × Nat) := {literal}\n'
body+='''theorem count : words.length=66 := rfl
theorem checked : ∀ entry∈words,checkSlot CapturedFullAssertions54.recipeAt entry.1=true := by
 simp only [words,List.forall_mem_cons]
 exact '''+conjunction([h+'.checked'for h in heads])+'''
theorem bits_checked : ∀ entry∈words,
 BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots entry.1 entry.2)=true := by
 simp only [words,List.forall_mem_cons]
 exact '''+conjunction([h+'.bits_checked'for h in heads])+'''
theorem positions : ∀ entry∈words,entry.1.position<22816 ∧ entry.2+entry.1.width≤22816 := by
 simp only [words,List.forall_mem_cons]
 exact '''+conjunction([h+'.positions'for h in heads])+'''
theorem originals : ∀ entry∈words,
 (3≤entry.1.start ∧ entry.1.start+entry.1.width≤22738) ∧
 (3≤entry.1.value ∧ entry.1.value<22738) := by
 simp only [words,List.forall_mem_cons]
 exact '''+conjunction([h+'.originals'for h in heads])+'''
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∀ entry∈words,∃ n : Nat,n<2^entry.1.width ∧ (n : F)=rho entry.1.value := by
 simp only [words,List.forall_mem_cons]
 exact '''+conjunction([h+'.sound rho satisfied'for h in heads])+'''
theorem shared_constructor (base : Nat → F) (flags : Nat → Bool) (seedColumns : List Nat)
 (numbers : Nat → Nat)
 (bounded : ∀ entry∈words,numbers entry.1.value<2^entry.1.width)
 (meanings : ∀ entry∈words,BooleanHints207.seeded base flags seedColumns entry.1.value=(numbers entry.1.value : F))
 (coverage : ∀ entry∈words,∀ column∈columns entry.1,column∈seedColumns)
 (encoding : ∀ entry∈words,(columns entry.1).map flags=encodeBits entry.1.width (numbers entry.1.value)) :
 ∀ entry∈words,∃ row,CapturedFullRelation58.rowAt (177954+entry.1.position)=some row ∧
 Square (eval (CapturedFullRelation58.candidate (BooleanHints207.seeded base flags seedColumns)) row.a)
        (eval (CapturedFullRelation58.candidate (BooleanHints207.seeded base flags seedColumns)) row.b) := by
 intro entry member
 exact SharedWordSeed212.shared_selected_value base flags seedColumns entry.1 (numbers entry.1.value)
   (bounded entry member) (meanings entry member) (coverage entry member) (encoding entry member)
   (originals entry member).1 (originals entry member).2 (positions entry member).1 (checked entry member)
end ShielddSecurity.CapturedWordRoot213
'''
audits=['words','count','checked','bits_checked','positions','originals','sound','shared_constructor']
inputs=[W/'mac-word-slots211-source01/generation01.json',W/'mac-word-slots211-source01/selected-data01.json',W/'mac-word-shared212-source02/source-root/ShielddSecurity/SharedWordSeed212.lean']+[Path(o['source']['path'])for o in g['outputs']]
S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-word-hints210-source03/generate.py').read_bytes())
(S/'templates01.json').write_text(json.dumps(dict(modules={'CapturedWordRoot213':dict(body=body,names=audits)},inputs={str(p):pin(p)for p in inputs},scope='SOURCE_ONLY_UNRUN eight planned reports. All66 actual reconstruction positions, including duplicate reconstruction rows and three parity overlaps. Arbitrary full relation derives bounded natural meanings; common candidate constructor retains independent natural bounds/seeded input meanings/finite bit coverage/Bool encoding compatibility. Does not assume desired row/hash truth or initial satisfaction. Encoding compatibility remains legal-witness obligation; all constructors act on one shared candidate. Other assertion families/native/full Transfer OPEN.'),sort_keys=True,separators=(',',':'))+'\n')
print(json.dumps(dict(stage=str(S),planned_audits=len(audits))))
