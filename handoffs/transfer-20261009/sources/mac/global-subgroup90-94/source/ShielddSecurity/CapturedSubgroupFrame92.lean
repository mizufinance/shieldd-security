import ShielddSecurity.CapturedFourSubgroupConstructor88
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedSubgroupFrame92
def Safe (column : Nat) : Prop := column<22738 ∧ column≠1 ∧ column≠2 ∧ column≠TransferFirstSubgroupData01.copy ∧
  ¬(49≤column ∧ column<135) ∧ column<184
instance safeDecidable (column : Nat) : Decidable (Safe column) := by
  unfold Safe
  infer_instance
def check (group : Fin 4) : Bool := (List.range 7).all
  (fun index => decide (Safe (CapturedSubgroupSelection87.rename group (14+index))))
theorem checked0 : check ⟨0,by decide⟩=true := by decide +kernel
theorem checked1 : check ⟨1,by decide⟩=true := by decide +kernel
theorem checked2 : check ⟨2,by decide⟩=true := by decide +kernel
theorem checked3 : check ⟨3,by decide⟩=true := by decide +kernel
theorem checked (group : Fin 4) : check group=true := by
  rcases group with ⟨group,bound⟩
  interval_cases group
  · exact checked0
  · exact checked1
  · exact checked2
  · exact checked3
theorem safe (group : Fin 4) (index : Nat) (lower : 14≤index) (upper : index≤20) :
    Safe (CapturedSubgroupSelection87.rename group index) := by
  have value:=of_decide_eq_true (List.all_eq_true.mp (checked group) (index-14) (List.mem_range.mpr (by omega)))
  have eqIndex : 14+(index-14)=index := by omega
  rw [eqIndex] at value
  exact value
end ShielddSecurity.CapturedSubgroupFrame92

set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupFrame92.Safe
#print axioms ShielddSecurity.CapturedSubgroupFrame92.Safe
set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupFrame92.safeDecidable
#print axioms ShielddSecurity.CapturedSubgroupFrame92.safeDecidable
set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupFrame92.check
#print axioms ShielddSecurity.CapturedSubgroupFrame92.check
set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupFrame92.checked0
#print axioms ShielddSecurity.CapturedSubgroupFrame92.checked0
set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupFrame92.checked1
#print axioms ShielddSecurity.CapturedSubgroupFrame92.checked1
set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupFrame92.checked2
#print axioms ShielddSecurity.CapturedSubgroupFrame92.checked2
set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupFrame92.checked3
#print axioms ShielddSecurity.CapturedSubgroupFrame92.checked3
set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupFrame92.checked
#print axioms ShielddSecurity.CapturedSubgroupFrame92.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupFrame92.safe
#print axioms ShielddSecurity.CapturedSubgroupFrame92.safe
