import ShielddSecurity.CapturedRegulatedBoolean76
import ShielddSecurity.MerkleBits29
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedGlobalPosition77
open CompilerArithmeticTransport41 CompilerAssertionBlock51
noncomputable def check : Bool := CompilerRowSlice63.check CapturedFullRelation58.rowAt 178083 34 MerkleBits29.actualRows
theorem checked : check=true := by decide +kernel
noncomputable def supportCheck : Bool := MerkleBits29.actualRows.all (fun row =>
  (row.a++row.b).all (fun term => decide (term.1=135 ∨ (184≤term.1 ∧ term.1<216))))
theorem support_checked : supportCheck=true := by decide +kernel
variable {F : Type} [Field F]
noncomputable def completed (base : Nat → F) (epoch position : Nat) : Nat → F :=
  CapturedGlobalRegistered74.completed (MerkleBits29.seed base position) epoch
theorem original_role (base : Nat → F) (position column : Nat) (outside : column<184 ∨ 216≤column) :
    MerkleBits29.seed base position column=base column := MerkleBits29.seed_outside base position column outside
theorem outside (base : Nat → F) (epoch position column : Nat)
    (arithmeticOutside : column<22738 ∨ 200692≤column)
    (notVerifier : column≠1 ∧ column≠2 ∧ column≠copy)
    (notEpochHints : ¬(49≤column ∧ column<135))
    (notPositionHints : column<184 ∨ 216≤column) :
    completed base epoch position column=base column :=
  (CapturedGlobalRegistered74.completed_outside _ epoch column arithmeticOutside notVerifier notEpochHints).trans
    (original_role base position column notPositionHints)
variable [CharP F p]
theorem full_position (rho : Nat → F)
    (sat : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) : ∃ n : Nat,n<2^32 ∧ (n:F)=rho 135 :=
  MerkleBits29.position_bound rho (CompilerRowSlice63.of_full_satisfies CapturedFullRelation58.rowAt 200770
    178083 34 MerkleBits29.actualRows checked (by decide) rho sat)
theorem position_assertions (base : Nat → F) (epoch position : Nat) (bound : position<2^32)
    (meaning : base 135=(position:F)) :
    SatisfiesAt (completed base epoch position) (fun index => CapturedFullRelation58.rowAt (178083+index)) 34 := by
  have seeded := MerkleBits29.seed_complete base position bound meaning
  have finalRows : Satisfies (completed base epoch position) MerkleBits29.actualRows := by
    intro row member
    have same (term : Nat×Int) (present : term∈row.a++row.b) :
        completed base epoch position term.1=MerkleBits29.seed base position term.1 := by
      have region:=of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp support_checked row member) term present)
      change CapturedGlobalRegistered74.completed _ epoch term.1=_
      apply CapturedGlobalRegistered74.completed_outside
      · omega
      · unfold copy; omega
      · omega
    have a:=eval_agrees (completed base epoch position) (MerkleBits29.seed base position) row.a
      (fun term present => same term (List.mem_append_left _ present))
    have b:=eval_agrees (completed base epoch position) (MerkleBits29.seed base position) row.b
      (fun term present => same term (List.mem_append_right _ present))
    change Square (eval (completed base epoch position) row.a) (eval (completed base epoch position) row.b)
    rw [a,b]
    exact seeded row member
  exact (CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt 178083 34
    MerkleBits29.actualRows checked _).mp finalRows
theorem legal_registry_global139 (c : TransferSem.Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.RegistrySem c w) (sinkMeaning : c.unregulatedRing=CapturedRegistryPointDomain75.sink)
    (base : Nat → F) (epoch : base 34=(w.registry.audit.epoch : F))
    (position : base 135=(w.registry.position : F))
    (regulated : base 10=(if w.regulated then 1 else 0))
    (px : base 35=(w.registry.audit.payload.x : F)) (py : base 36=(w.registry.audit.payload.y : F))
    (cx : base 42=(w.registry.audit.checking.x : F)) (cy : base 43=(w.registry.audit.checking.y : F))
    (zero : base 0=1) :
    SatisfiesAt (completed base w.registry.audit.epoch w.registry.position) CapturedFullArithmetic52.rowAt 177954 ∧
    SatisfiesAt (completed base w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (177979+index)) 104 ∧
    SatisfiesAt (completed base w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (177954+index)) 1 ∧
    SatisfiesAt (completed base w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (178083+index)) 34 := by
  have e : MerkleBits29.seed base w.registry.position 34=(w.registry.audit.epoch:F) :=
    (original_role base _ 34 (by decide)).trans epoch
  have r : MerkleBits29.seed base w.registry.position 10=(if w.regulated then 1 else 0) :=
    (original_role base _ 10 (by decide)).trans regulated
  have pxx : MerkleBits29.seed base w.registry.position 35=(w.registry.audit.payload.x:F) :=
    (original_role base _ 35 (by decide)).trans px
  have pyy : MerkleBits29.seed base w.registry.position 36=(w.registry.audit.payload.y:F) :=
    (original_role base _ 36 (by decide)).trans py
  have cxx : MerkleBits29.seed base w.registry.position 42=(w.registry.audit.checking.x:F) :=
    (original_role base _ 42 (by decide)).trans cx
  have cyy : MerkleBits29.seed base w.registry.position 43=(w.registry.audit.checking.y:F) :=
    (original_role base _ 43 (by decide)).trans cy
  have z : MerkleBits29.seed base w.registry.position 0=1 := (original_role base _ 0 (by decide)).trans zero
  have first:=CapturedRegulatedBoolean76.legal_registry_global105 c w legal sinkMeaning
    (MerkleBits29.seed base w.registry.position) e r pxx pyy cxx cyy z
  exact ⟨first.1,first.2.1,first.2.2,position_assertions base _ _ legal.2.2.2.2.2.1 position⟩
end ShielddSecurity.CapturedGlobalPosition77
