from pathlib import Path
import json,sys,hashlib
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-boolean-root209-source02'
def require(v,m):
 if not v:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags');require(not S.exists(),'immutable source')
g=json.loads((W/'mac-boolean-slots208-source01/generation01.json').read_bytes());ns=[o['name']for o in g['outputs']]
def tree(v,join):
 if len(v)==1:return v[0]
 mid=len(v)//2;return join(tree(v[:mid],join),tree(v[mid:],join))
expr=tree([n+'.slots'for n in ns],lambda l,r:'('+l+'++'+r+')');pairs=lambda key:tree([n+'.'+key for n in ns],lambda l,r:'⟨'+l+','+r+'⟩')
body=''.join('import ShielddSecurity.'+n+'\n'for n in ns)+'''set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanRoot209
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
'''+f'def slots : List (Nat × Nat) := {expr}\n'
body+='''def columns : List Nat := slots.map Prod.snd
'''+'''theorem count : slots.length=10783 := by
 simp only [slots,List.length_append,'''+','.join(n+'.count'for n in ns)+''']
'''+'''theorem checked : checkSlots CapturedFullAssertions54.recipeAt slots=true := by
 simp only [slots,checkSlots_append,'''+','.join(n+'.checked'for n in ns)+''',Bool.true_and]
'''+'''theorem originals : ∀ slot∈slots,3≤slot.2 ∧ slot.2<22738 := by
 simp only [slots,List.forall_mem_append]
 exact '''+pairs('originals')+'''
theorem positions : ∀ slot∈slots,slot.1<22816 := by
 simp only [slots,List.forall_mem_append]
 exact '''+pairs('positions')+'''
theorem coverage (slot : Nat × Nat) (member : slot∈slots) : slot.2∈columns :=
 List.mem_map.mpr ⟨slot,member,rfl⟩
theorem columns_outside (column : Nat) (outside : column<3 ∨ 22738≤column) : column∉columns := by
 intro member
 obtain ⟨slot,known,same⟩:=List.mem_map.mp member
 have bounds:=originals slot known
 change slot.2=column at same
 omega
variable {F : Type} [Field F]
noncomputable def seeded (base : Nat → F) (bits : Nat → Bool) : Nat → F :=
 BooleanHints207.seeded base bits columns
theorem seeded_fixed (base : Nat → F) (bits : Nat → Bool) :
 seeded base bits 0=base 0 ∧ seeded base bits 1=base 1 ∧ seeded base bits 2=base 2 ∧
 seeded base bits copy=base copy :=
 ⟨seeded_outside base bits columns 0 (columns_outside 0 (by decide)),
 seeded_outside base bits columns 1 (columns_outside 1 (by decide)),
 seeded_outside base bits columns 2 (columns_outside 2 (by decide)),
 seeded_outside base bits columns copy (columns_outside copy (by decide))⟩
variable [CharP F p]
noncomputable def completed (base : Nat → F) (bits : Nat → Bool) : Nat → F :=
 CapturedFullRelation58.candidate (seeded base bits)
theorem arithmetic (base : Nat → F) (bits : Nat → Bool) :
 CompilerArithmeticBlock44.SatisfiesAt (completed base bits) CapturedFullArithmetic52.rowAt 177954 :=
 CapturedFullRelation58.candidate_arithmetic (seeded base bits)
theorem selected (base : Nat → F) (bits : Nat → Bool) : ∀ slot∈slots,
 ∃ row,CapturedFullRelation58.rowAt (177954+slot.1)=some row ∧
 Square (eval (completed base bits) row.a) (eval (completed base bits) row.b) :=
 fun slot member => candidate_selected base bits columns slots checked originals coverage positions slot member
omit [CharP F p] in
theorem unselected_input (base : Nat → F) (bits : Nat → Bool) (input : Nat)
 (bound : input<22735) (outside : 3+input∉columns) : completed base bits (3+input)=base (3+input) :=
 (CapturedFullRelation58.candidate_inputs (seeded base bits) input bound).trans
   (seeded_outside base bits columns (3+input) outside)
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∀ slot∈slots,rho slot.2=0 ∨ rho slot.2=1 := by
 intro slot member
 obtain ⟨outlined,matching⟩:=checked_slot _ slots checked slot member
 have truth:=((CapturedFullRelation58.satisfies_iff rho).mp satisfied).2 slot.1
   (positions slot member) (outlined,wireRecipe slot.2) matching
 exact (wire_truth rho slot.2).mp truth
end ShielddSecurity.CapturedBooleanRoot209
'''
names=['slots','columns','count','checked','originals','positions','coverage','columns_outside','seeded','seeded_fixed','completed','arithmetic','selected','unselected_input','sound']
pins=[W/'mac-boolean-hints207-source05/source-root/ShielddSecurity/BooleanHints207.lean',W/'mac-boolean-slots208-source01/selected-data01.json',W/'mac-boolean-slots208-source01/generation01.json']+[Path(o['source']['path'])for o in g['outputs']]
S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-indexed-slices183-source01/generate.py').read_bytes())
(S/'templates01.json').write_text(json.dumps(dict(modules={'CapturedBooleanRoot209':dict(body=body,names=names)},inputs={str(p):pin(p)for p in pins},scope='SOURCE_ONLY_UNRUN. Balanced exact10783-original-Boolean-slot constructor with all177954 arithmetic on ONE assignment, plus arbitrary full-relation Boolean recovery. Explicit Bool function sets selected original hint/user columns; other originals fixed. Word reconstruction/semantic-role consistency and fresh51208 Boolean remain OPEN. No full assertion/Transfer/native conclusion. All15 planned reports UNRUN.'),sort_keys=True,separators=(',',':'))+'\n')
