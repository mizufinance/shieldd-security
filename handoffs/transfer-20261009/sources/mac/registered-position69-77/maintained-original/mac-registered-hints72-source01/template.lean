import ShielddSecurity.CapturedRegisteredAudit71
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegisteredHints72
open Compiler CompilerArithmeticTransport41
variable {F : Type} [Field F]
noncomputable def zeroSupportCheck : Bool := (List.range 10).all (fun index =>
  (CapturedRegisteredAudit70.zeroTerms index).all (fun entry => decide (entry.1<115)))
theorem zero_support_checked : zeroSupportCheck=true := by decide +kernel
theorem zero_support (index : Nat) (bound : index<10) (entry : Nat × Int)
    (member : entry ∈ CapturedRegisteredAudit70.zeroTerms index) : entry.1<115 := by
  have h:=List.all_eq_true.mp zero_support_checked index (List.mem_range.mpr bound)
  exact of_decide_eq_true (List.all_eq_true.mp h entry member)
noncomputable def seeded (base : Nat → F) : Nat → F := fun column =>
  if 115≤column ∧ column<135 then
    if column%2=1 then CompilerZeroTest65.indicator (eval base (CapturedRegisteredAudit70.zeroTerms ((column-115)/2)))
    else (eval base (CapturedRegisteredAudit70.zeroTerms ((column-116)/2)))⁻¹
  else base column
theorem seeded_outside (base : Nat → F) (column : Nat) (outside : ¬(115≤column ∧ column<135)) :
    seeded base column=base column := by simp only [seeded,if_neg outside]
theorem seeded_values (base : Nat → F) (index : Nat) (bound : index<10) :
    seeded base (115+2*index)=CompilerZeroTest65.indicator (eval base (CapturedRegisteredAudit70.zeroTerms index)) ∧
    seeded base (116+2*index)=(eval base (CapturedRegisteredAudit70.zeroTerms index))⁻¹ := by
  have az : 115≤115+2*index ∧ 115+2*index<135 := by omega
  have ai : 115≤116+2*index ∧ 116+2*index<135 := by omega
  have odd : (115+2*index)%2=1 := by omega
  have even : ¬(116+2*index)%2=1 := by omega
  have zindex : (115+2*index-115)/2=index := by omega
  have iindex : (116+2*index-116)/2=index := by omega
  exact ⟨by simp only [seeded,if_pos az,if_pos odd,zindex],
    by simp only [seeded,if_pos ai,if_neg even,iindex]⟩
theorem eval_frame (rho sigma : Nat → F) (terms : Linear)
    (same : ∀ column coefficient,(column,coefficient) ∈ terms → rho column=sigma column) :
    eval rho terms=eval sigma terms := by
  induction terms with
  | nil => rfl
  | cons entry tail ih =>
    rcases entry with ⟨column,coefficient⟩
    have head:=same column coefficient (List.mem_cons_self)
    have rest:=ih (fun c k member => same c k (List.mem_cons_of_mem _ member))
    simp only [eval,head,rest]
theorem eval_seeded (base : Nat → F) (index : Nat) (bound : index<10) :
    eval (seeded base) (CapturedRegisteredAudit70.zeroTerms index)=eval base (CapturedRegisteredAudit70.zeroTerms index) := by
  apply eval_frame
  intro column coefficient member
  exact seeded_outside base column (by have h:=zero_support index bound (column,coefficient) member; omega)
theorem seeded_primitive (base : Nat → F) : CapturedRegisteredAudit70.Primitive (seeded base) := by
  intro index bound
  have hints:=seeded_values base index bound
  rw [hints.1,hints.2,eval_seeded base index bound]
  exact CompilerZeroTest65.complete _
theorem primitive_frame (rho sigma : Nat → F) (same : ∀ column<135,rho column=sigma column)
    (truth : CapturedRegisteredAudit70.Primitive rho) : CapturedRegisteredAudit70.Primitive sigma := by
  intro index bound
  have value : eval rho (CapturedRegisteredAudit70.zeroTerms index)=eval sigma (CapturedRegisteredAudit70.zeroTerms index) := by
    apply eval_frame
    intro column coefficient member
    exact same column (lt_trans (zero_support index bound (column,coefficient) member) (by decide))
  rw [←value,←same (115+2*index) (by omega),←same (116+2*index) (by omega)]
  exact truth index bound
def LegalGuards (base : Nat → F) : Prop := ∀ pair<5,
  eval base (CapturedRegisteredAudit70.zeroTerms (2*pair))=0 ∧
  eval base (CapturedRegisteredAudit70.zeroTerms (2*pair+1))=0 → base 10=0
theorem seeded_guards (base : Nat → F) (legal : LegalGuards base) :
    CapturedRegisteredAudit71.Guards (seeded base) := by
  intro pair bound
  have primitive:=seeded_primitive base
  have checked:=CompilerCoordinateZero69.guard_iff
    (eval (seeded base) (CapturedRegisteredAudit70.zeroTerms (2*pair)))
    (eval (seeded base) (CapturedRegisteredAudit70.zeroTerms (2*pair+1)))
    (seeded base (115+2*(2*pair))) (seeded base (116+2*(2*pair)))
    (seeded base (115+2*(2*pair+1))) (seeded base (116+2*(2*pair+1))) (seeded base 10)
    ⟨primitive (2*pair) (by omega),primitive (2*pair+1) (by omega)⟩
  have h : seeded base 10*(seeded base (115+2*(2*pair))*seeded base (115+2*(2*pair+1)))=0 := by
    apply checked.mpr
    rw [eval_seeded base (2*pair) (by omega),eval_seeded base (2*pair+1) (by omega),seeded_outside base 10 (by omega)]
    exact legal pair bound
  have leftIndex : 115+2*(2*pair)=115+4*pair := by omega
  have rightIndex : 115+2*(2*pair+1)=117+4*pair := by omega
  simpa only [leftIndex,rightIndex] using h
theorem guards_frame (rho sigma : Nat → F) (same : ∀ column<135,rho column=sigma column)
    (truth : CapturedRegisteredAudit71.Guards rho) : CapturedRegisteredAudit71.Guards sigma := by
  intro pair bound
  rw [←same 10 (by decide),←same (115+4*pair) (by omega),←same (117+4*pair) (by omega)]
  exact truth pair bound
end ShielddSecurity.CapturedRegisteredHints72
