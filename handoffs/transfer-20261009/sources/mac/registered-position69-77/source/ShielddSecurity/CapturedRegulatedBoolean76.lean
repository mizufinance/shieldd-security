import ShielddSecurity.CapturedRegistryPointDomain75
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegulatedBoolean76
open CompilerArithmeticTransport41 CompilerAssertionBlock51
noncomputable def rows : List Row := [booleanRow 10]
noncomputable def check : Bool := CompilerRowSlice63.check CapturedFullRelation58.rowAt 177954 1 rows
theorem checked : check=true := by decide +kernel
variable {F : Type} [Field F]
theorem row_iff (rho : Nat → F) : Satisfies rho rows ↔ rho 10=0 ∨ rho 10=1 := by
  constructor
  · intro sat
    have h:=sat (booleanRow 10) (by simp [rows])
    exact boolean_sound (rho 10) (by simpa [booleanRow,eval] using h)
  · intro bit row member
    have shape : row=booleanRow 10 := by simpa only [rows,List.mem_singleton] using member
    subst row
    rcases bit with z|o
    · simp [booleanRow,eval,Square,z]
    · simp [booleanRow,eval,Square,o]
theorem full_boolean (rho : Nat → F)
    (sat : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) : rho 10=0 ∨ rho 10=1 :=
  (row_iff rho).mp (CompilerRowSlice63.of_full_satisfies CapturedFullRelation58.rowAt 200770 177954 1 rows
    checked (by decide) rho sat)
theorem completed_boolean (base : Nat → F) (n : Nat) (bit : base 10=0 ∨ base 10=1) :
    Satisfies (CapturedGlobalRegistered74.completed base n) rows := by
  apply (row_iff _).mpr
  rw [CapturedGlobalRegistered74.completed_outside base n 10 (by decide) (by decide) (by decide)]
  exact bit
variable [CharP F p]
theorem legal_registry_global105 (c : TransferSem.Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.RegistrySem c w) (sinkMeaning : c.unregulatedRing=CapturedRegistryPointDomain75.sink)
    (base : Nat → F) (epoch : base 34=(w.registry.audit.epoch : F))
    (regulated : base 10=(if w.regulated then 1 else 0))
    (px : base 35=(w.registry.audit.payload.x : F)) (py : base 36=(w.registry.audit.payload.y : F))
    (cx : base 42=(w.registry.audit.checking.x : F)) (cy : base 43=(w.registry.audit.checking.y : F))
    (zero : base 0=1) :
    SatisfiesAt (CapturedGlobalRegistered74.completed base w.registry.audit.epoch)
      CapturedFullArithmetic52.rowAt 177954 ∧
    SatisfiesAt (CapturedGlobalRegistered74.completed base w.registry.audit.epoch)
      (fun index => CapturedFullRelation58.rowAt (177979+index)) 104 ∧
    SatisfiesAt (CapturedGlobalRegistered74.completed base w.registry.audit.epoch)
      (fun index => CapturedFullRelation58.rowAt (177954+index)) 1 := by
  refine ⟨CapturedGlobalRegistered74.completed_arithmetic base w.registry.audit.epoch,
    CapturedRegistryPointDomain75.legal_registry_global104 c w legal sinkMeaning base epoch regulated px py cx cy zero,?_⟩
  have bit : base 10=0 ∨ base 10=1 := by
    cases h:w.regulated with
    | false => exact Or.inl (by simpa only [h] using regulated)
    | true => exact Or.inr (by simpa only [h] using regulated)
  exact (CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt 177954 1 rows checked _).mp
    (completed_boolean base w.registry.audit.epoch bit)
end ShielddSecurity.CapturedRegulatedBoolean76

set_option pp.all true in
#check @ShielddSecurity.CapturedRegulatedBoolean76.rows
#print axioms ShielddSecurity.CapturedRegulatedBoolean76.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedRegulatedBoolean76.check
#print axioms ShielddSecurity.CapturedRegulatedBoolean76.check
set_option pp.all true in
#check @ShielddSecurity.CapturedRegulatedBoolean76.checked
#print axioms ShielddSecurity.CapturedRegulatedBoolean76.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedRegulatedBoolean76.row_iff
#print axioms ShielddSecurity.CapturedRegulatedBoolean76.row_iff
set_option pp.all true in
#check @ShielddSecurity.CapturedRegulatedBoolean76.full_boolean
#print axioms ShielddSecurity.CapturedRegulatedBoolean76.full_boolean
set_option pp.all true in
#check @ShielddSecurity.CapturedRegulatedBoolean76.completed_boolean
#print axioms ShielddSecurity.CapturedRegulatedBoolean76.completed_boolean
set_option pp.all true in
#check @ShielddSecurity.CapturedRegulatedBoolean76.legal_registry_global105
#print axioms ShielddSecurity.CapturedRegulatedBoolean76.legal_registry_global105
