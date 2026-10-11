from pathlib import Path
import json,hashlib,sys,runpy,os
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-full-arithmetic45-execution245';S=W/'mac-shared-word-witness221-source03'
def require(c,m):
 if not c:raise RuntimeError(m)
def pin(p):
 b=Path(p).read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated preparation');require(not S.exists(),'new immutable SOURCE');g=runpy.run_path(str(P/'maintained/guard.py'),run_name='READ_ONLY');c=g['read_config'](str(P/'config01.json'),pin(P/'config01.json')['sha256']);mods=json.loads(Path(c['closure']['path']).read_bytes())['modules'];mods.update(c['qualified_batch_imports']);rp=P/'runtime/receipts/1281-SharedWordFlags220.json';r=json.loads(rp.read_bytes());require(r['status']=='passed'and r['exit']==0 and r['cleanup']['clean'],'qualified220');mods['SharedWordFlags220']=dict(source=r['source'],object=next(iter(r['objects'].values())),receipt=pin(rp),current_slots={})
inputs={}
for n in ['SharedWordFlags220','CapturedWordRoot213','CapturedBooleanRoot209']:
 d=mods[n]
 for v in [d['source'],d['object'],d['receipt'],*filter(None,d['current_slots'].values())]:require(pin(v['path'])==v,'exact qualified direct input');inputs[v['path']]=v
body='''import ShielddSecurity.CapturedWordRoot213
import ShielddSecurity.CapturedBooleanRoot209
import ShielddSecurity.SharedWordFlags220
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedWordWitness221
open WordHints210 CompilerAssertionBlock51 CompilerArithmeticTransport41
def wordSlots : List Slot := CapturedWordRoot213.words.map Prod.fst
def seedColumns : List Nat := CapturedBooleanRoot209.columns ++ wordSlots.flatMap WordHints210.columns
def bits (numbers : Nat → Nat) (fallback : Nat → Bool) : Nat → Bool :=
 SharedWordFlags220.flags wordSlots numbers fallback
theorem word_coverage (entry : Slot × Nat) (member : entry∈CapturedWordRoot213.words)
 (column : Nat) (present : column∈WordHints210.columns entry.1) : column∈seedColumns :=
 List.mem_append_right _ (List.mem_flatMap.mpr ⟨entry.1,List.mem_map.mpr ⟨entry,member,rfl⟩,present⟩)
theorem boolean_coverage (slot : Nat × Nat) (member : slot∈CapturedBooleanRoot209.slots) :
 slot.2∈seedColumns := List.mem_append_left _ (CapturedBooleanRoot209.coverage slot member)
theorem columns_outside (column : Nat) (outside : column<3 ∨ 22738≤column) : column∉seedColumns := by
 intro member
 rcases List.mem_append.mp member with boolean|word
 · exact CapturedBooleanRoot209.columns_outside column outside boolean
 · obtain ⟨slot,known,present⟩:=List.mem_flatMap.mp word
   obtain ⟨entry,member,equal⟩:=List.mem_map.mp known
   subst slot
   have bound:=(CapturedWordRoot213.originals entry member).1
   obtain ⟨offset,before,equal⟩:=List.mem_range'.mp present
   simp only [Nat.one_mul] at equal
   omega
theorem encoded (numbers : Nat → Nat) (fallback : Nat → Bool)
 (coherent : SharedWordFlags220.Coherent (SharedWordFlags220.assignments wordSlots numbers))
 (entry : Slot × Nat) (member : entry∈CapturedWordRoot213.words) :
 (WordHints210.columns entry.1).map (bits numbers fallback)=encodeBits entry.1.width (numbers entry.1.value) :=
 SharedWordFlags220.encoded wordSlots numbers fallback coherent entry.1
   (List.mem_map.mpr ⟨entry,member,rfl⟩)
variable {F : Type} [Field F]
noncomputable def seeded (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) : Nat → F :=
 BooleanHints207.seeded base (bits numbers fallback) seedColumns
theorem seeded_fixed (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) :
 seeded base numbers fallback 0=base 0 ∧ seeded base numbers fallback 1=base 1 ∧
 seeded base numbers fallback 2=base 2 ∧ seeded base numbers fallback copy=base copy :=
 ⟨BooleanHints207.seeded_outside base _ seedColumns 0 (columns_outside 0 (by decide)),
 BooleanHints207.seeded_outside base _ seedColumns 1 (columns_outside 1 (by decide)),
 BooleanHints207.seeded_outside base _ seedColumns 2 (columns_outside 2 (by decide)),
 BooleanHints207.seeded_outside base _ seedColumns copy (columns_outside copy (by decide))⟩
variable [CharP F p]
noncomputable def completed (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) : Nat → F :=
 CapturedFullRelation58.candidate (seeded base numbers fallback)
theorem arithmetic (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) :
 CompilerArithmeticBlock44.SatisfiesAt (completed base numbers fallback) CapturedFullArithmetic52.rowAt 177954 :=
 CapturedFullRelation58.candidate_arithmetic (seeded base numbers fallback)
theorem boolean_rows (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) :
 ∀ slot∈CapturedBooleanRoot209.slots,∃ row,CapturedFullRelation58.rowAt (177954+slot.1)=some row ∧
 Square (eval (completed base numbers fallback) row.a) (eval (completed base numbers fallback) row.b) :=
 BooleanHints207.candidate_selected base (bits numbers fallback) seedColumns CapturedBooleanRoot209.slots
 CapturedBooleanRoot209.checked CapturedBooleanRoot209.originals boolean_coverage CapturedBooleanRoot209.positions
theorem word_rows (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
 (coherent : SharedWordFlags220.Coherent (SharedWordFlags220.assignments wordSlots numbers))
 (bounded : ∀ entry∈CapturedWordRoot213.words,numbers entry.1.value<2^entry.1.width)
 (meanings : ∀ entry∈CapturedWordRoot213.words,seeded base numbers fallback entry.1.value=(numbers entry.1.value : F)) :
 ∀ entry∈CapturedWordRoot213.words,∃ row,CapturedFullRelation58.rowAt (177954+entry.1.position)=some row ∧
 Square (eval (completed base numbers fallback) row.a) (eval (completed base numbers fallback) row.b) :=
 CapturedWordRoot213.shared_constructor base (bits numbers fallback) seedColumns numbers
 bounded meanings word_coverage (encoded numbers fallback coherent)
omit [CharP F p] in
theorem unselected_input (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
 (input : Nat) (bound : input<22735) (outside : 3+input∉seedColumns) :
 completed base numbers fallback (3+input)=base (3+input) :=
 (CapturedFullRelation58.candidate_inputs (seeded base numbers fallback) input bound).trans
 (BooleanHints207.seeded_outside base _ seedColumns (3+input) outside)
omit [CharP F p] in
theorem links (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) :
 completed base numbers fallback 1=completed base numbers fallback 22737 ∧
 completed base numbers fallback 2=completed base numbers fallback 9 ∧
 completed base numbers fallback copy=completed base numbers fallback 0 :=
 CapturedFullRelation58.candidate_links (seeded base numbers fallback)
end ShielddSecurity.SharedWordWitness221
'''
names=['wordSlots','seedColumns','bits','word_coverage','boolean_coverage','columns_outside','encoded','seeded','seeded_fixed','completed','arithmetic','boolean_rows','word_rows','unselected_input','links']
st=os.statvfs(W);require(st.f_bavail*st.f_frsize>2*1024**3+1024**2,'source disk reserve');S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-shared-word-flags220-source04/generate.py').read_bytes());(S/'templates01.json').write_text(json.dumps(dict(modules={'SharedWordWitness221':dict(body=body,names=names)},inputs=inputs,scope='SOURCE_ONLY_UNRUN. One candidate for all177954 arithmetic,10783 actual Boolean positions and66 weighted reconstruction records. Replaces arbitrary common flag encoding premise by constructive map with explicit overlap agreement. Natural bounds and seeded field input meanings remain; three parity value columns are intentionally selected bits. No union with1467 previous constructor or total legal witness/native/full Transfer claim.'),sort_keys=True,separators=(',',':'))+'\n')
