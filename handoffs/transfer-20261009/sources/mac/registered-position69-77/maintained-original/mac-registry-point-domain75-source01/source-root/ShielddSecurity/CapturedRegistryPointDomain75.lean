import ShielddSecurity.CapturedGlobalRegistered74
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistryPointDomain75
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
def sink : TransferCore.Affine := ⟨49822839976625491399435002605169580882773999909559575334089637637825427273330,29108985603249989484651727880329493522712908252517904247459350893053326313050⟩
def meaningTerms (index : Nat) : Linear := ([[(35,1)],[(0,-1),(36,1)],[(0,-49822839976625491399435002605169580882773999909559575334089637637825427273330),(35,1)],[(0,-29108985603249989484651727880329493522712908252517904247459350893053326313050),(36,1)],[(35,1),(42,-1)],[(36,1),(43,-1)],[(42,1)],[(0,-1),(43,1)],[(0,-49822839976625491399435002605169580882773999909559575334089637637825427273330),(42,1)],[(0,-29108985603249989484651727880329493522712908252517904247459350893053326313050),(43,1)]]).getD index []
noncomputable def meaningCheck : Bool := (List.range 10).all (fun index =>
  decide (canonical p (CapturedRegisteredAudit70.zeroTerms index)=canonical p (meaningTerms index)))
theorem meaning_checked : meaningCheck=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem meaning_value (rho : Nat → F) (index : Nat) (bound : index<10) :
    eval rho (CapturedRegisteredAudit70.zeroTerms index)=eval rho (meaningTerms index) :=
  canonical_equal rho _ _ (of_decide_eq_true (List.all_eq_true.mp meaning_checked index (List.mem_range.mpr bound)))
theorem point_cast_equal (left right : TransferCore.Affine)
    (leftCanonical : TransferCore.CanonicalAffine left)
    (rightCanonical : TransferCore.CanonicalAffine right)
    (hx : (left.x : F)-(right.x : F)=0) (hy : (left.y : F)-(right.y : F)=0) : left=right := by
  have xeq : left.x=right.x := CapturedEpochHints62.cast_small_unique _ _ leftCanonical.1 rightCanonical.1 (sub_eq_zero.mp hx)
  have yeq : left.y=right.y := CapturedEpochHints62.cast_small_unique _ _ leftCanonical.2 rightCanonical.2 (sub_eq_zero.mp hy)
  cases left
  cases right
  cases xeq
  cases yeq
  rfl
theorem field_guards (base : Nat → F) (payload checking : TransferCore.Affine)
    (payloadCanonical : TransferCore.CanonicalAffine payload)
    (checkingCanonical : TransferCore.CanonicalAffine checking)
    (px : base 35=(payload.x : F)) (py : base 36=(payload.y : F))
    (cx : base 42=(checking.x : F)) (cy : base 43=(checking.y : F)) (zero : base 0=1)
    (excluded : base 10≠0 → payload≠⟨0,1⟩ ∧ checking≠⟨0,1⟩ ∧
      payload≠sink ∧ checking≠sink ∧ payload≠checking) :
    CapturedRegisteredHints72.LegalGuards base := by
  intro pair bound equal
  by_cases flagZero : base 10=0
  · exact flagZero
  · have forbidden:=excluded flagZero
    rcases (show pair=0 ∨ pair=1 ∨ pair=2 ∨ pair=3 ∨ pair=4 by omega) with rfl|rfl|rfl|rfl|rfl
    · have hx : (payload.x : F)-((⟨0,1⟩ : TransferCore.Affine).x : F)=0 := by
        have h:=equal.1
        rw [meaning_value base 0 (by decide)] at h
        simpa [meaningTerms,eval,sink,zero,px,py,cx,cy,sub_eq_add_neg,add_comm] using h
      have hy : (payload.y : F)-((⟨0,1⟩ : TransferCore.Affine).y : F)=0 := by
        have h:=equal.2
        rw [meaning_value base 1 (by decide)] at h
        simpa [meaningTerms,eval,sink,zero,px,py,cx,cy,sub_eq_add_neg,add_comm] using h
      exact False.elim (forbidden.1 (point_cast_equal payload (⟨0,1⟩ : TransferCore.Affine) payloadCanonical (by decide) hx hy))
    · have hx : (payload.x : F)-(sink.x : F)=0 := by
        have h:=equal.1
        rw [meaning_value base 2 (by decide)] at h
        simpa [meaningTerms,eval,sink,zero,px,py,cx,cy,sub_eq_add_neg,add_comm] using h
      have hy : (payload.y : F)-(sink.y : F)=0 := by
        have h:=equal.2
        rw [meaning_value base 3 (by decide)] at h
        simpa [meaningTerms,eval,sink,zero,px,py,cx,cy,sub_eq_add_neg,add_comm] using h
      exact False.elim (forbidden.2.2.1 (point_cast_equal payload sink payloadCanonical (by decide) hx hy))
    · have hx : (payload.x : F)-(checking.x : F)=0 := by
        have h:=equal.1
        rw [meaning_value base 4 (by decide)] at h
        simpa [meaningTerms,eval,sink,zero,px,py,cx,cy,sub_eq_add_neg,add_comm] using h
      have hy : (payload.y : F)-(checking.y : F)=0 := by
        have h:=equal.2
        rw [meaning_value base 5 (by decide)] at h
        simpa [meaningTerms,eval,sink,zero,px,py,cx,cy,sub_eq_add_neg,add_comm] using h
      exact False.elim (forbidden.2.2.2.2 (point_cast_equal payload checking payloadCanonical checkingCanonical hx hy))
    · have hx : (checking.x : F)-((⟨0,1⟩ : TransferCore.Affine).x : F)=0 := by
        have h:=equal.1
        rw [meaning_value base 6 (by decide)] at h
        simpa [meaningTerms,eval,sink,zero,px,py,cx,cy,sub_eq_add_neg,add_comm] using h
      have hy : (checking.y : F)-((⟨0,1⟩ : TransferCore.Affine).y : F)=0 := by
        have h:=equal.2
        rw [meaning_value base 7 (by decide)] at h
        simpa [meaningTerms,eval,sink,zero,px,py,cx,cy,sub_eq_add_neg,add_comm] using h
      exact False.elim (forbidden.2.1 (point_cast_equal checking (⟨0,1⟩ : TransferCore.Affine) checkingCanonical (by decide) hx hy))
    · have hx : (checking.x : F)-(sink.x : F)=0 := by
        have h:=equal.1
        rw [meaning_value base 8 (by decide)] at h
        simpa [meaningTerms,eval,sink,zero,px,py,cx,cy,sub_eq_add_neg,add_comm] using h
      have hy : (checking.y : F)-(sink.y : F)=0 := by
        have h:=equal.2
        rw [meaning_value base 9 (by decide)] at h
        simpa [meaningTerms,eval,sink,zero,px,py,cx,cy,sub_eq_add_neg,add_comm] using h
      exact False.elim (forbidden.2.2.2.1 (point_cast_equal checking sink checkingCanonical (by decide) hx hy))
theorem prepared_role (base : Nat → F) (n column : Nat) (bound : column<49)
    (notVerifier : column≠1 ∧ column≠2 ∧ column≠copy) :
    CapturedGlobalEpoch64.prepared base n column=base column := by
  change CapturedEpochHints62.seeded (CompilerVerifierLinks53.seeded base) n column=base column
  rw [CapturedEpochHints62.seeded_outside _ n column (by omega),CompilerVerifierLinks53.seeded_outside base column notVerifier]
theorem registry_coordinate_guards (c : TransferSem.Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.RegistrySem c w) (sinkMeaning : c.unregulatedRing=sink)
    (base : Nat → F) (n : Nat) (regulated : base 10=(if w.regulated then 1 else 0))
    (px : base 35=(w.registry.audit.payload.x : F)) (py : base 36=(w.registry.audit.payload.y : F))
    (cx : base 42=(w.registry.audit.checking.x : F)) (cy : base 43=(w.registry.audit.checking.y : F))
    (zero : base 0=1) : CapturedRegisteredHints72.LegalGuards (CapturedGlobalEpoch64.prepared base n) := by
  have payloadCanonical:=legal.2.2.1.1
  have checkingCanonical:=legal.2.2.2.1.1
  apply field_guards (CapturedGlobalEpoch64.prepared base n) w.registry.audit.payload w.registry.audit.checking
    payloadCanonical checkingCanonical
    ((prepared_role base n 35 (by decide) (by decide)).trans px)
    ((prepared_role base n 36 (by decide) (by decide)).trans py)
    ((prepared_role base n 42 (by decide) (by decide)).trans cx)
    ((prepared_role base n 43 (by decide) (by decide)).trans cy)
    ((prepared_role base n 0 (by decide) (by decide)).trans zero)
  intro notZero
  have flag : base 10≠0 := fun h => notZero ((prepared_role base n 10 (by decide) (by decide)).trans h)
  have isTrue : w.regulated=true := by
    cases bit:w.regulated with
    | false => exact False.elim (flag (by simpa only [bit] using regulated))
    | true => rfl
  have branch:=legal.2.2.2.2.2.2.2.2.2.2
  rw [isTrue] at branch
  exact ⟨branch.2.2.1,branch.2.2.2.1,
    by simpa only [sinkMeaning] using branch.2.2.2.2.1,
    by simpa only [sinkMeaning] using branch.2.2.2.2.2.1,branch.2.2.2.2.2.2⟩
theorem legal_registry_global104 (c : TransferSem.Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.RegistrySem c w) (sinkMeaning : c.unregulatedRing=sink)
    (base : Nat → F) (epoch : base 34=(w.registry.audit.epoch : F))
    (regulated : base 10=(if w.regulated then 1 else 0))
    (px : base 35=(w.registry.audit.payload.x : F)) (py : base 36=(w.registry.audit.payload.y : F))
    (cx : base 42=(w.registry.audit.checking.x : F)) (cy : base 43=(w.registry.audit.checking.y : F))
    (zero : base 0=1) :
    SatisfiesAt (CapturedGlobalRegistered74.completed base w.registry.audit.epoch)
      (fun index => CapturedFullRelation58.rowAt (177979+index)) 104 :=
  CapturedGlobalRegistered74.completed_global104 base w.registry.audit.epoch
    (CapturedRegistryEpoch66.registry_epoch_bound c w legal) epoch
    (CapturedRegistryEpoch66.registry_guard c w legal base epoch regulated) zero
    (registry_coordinate_guards c w legal sinkMeaning base w.registry.audit.epoch regulated px py cx cy zero)
end ShielddSecurity.CapturedRegistryPointDomain75

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryPointDomain75.sink
#print axioms ShielddSecurity.CapturedRegistryPointDomain75.sink
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryPointDomain75.meaningTerms
#print axioms ShielddSecurity.CapturedRegistryPointDomain75.meaningTerms
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryPointDomain75.meaningCheck
#print axioms ShielddSecurity.CapturedRegistryPointDomain75.meaningCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryPointDomain75.meaning_checked
#print axioms ShielddSecurity.CapturedRegistryPointDomain75.meaning_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryPointDomain75.meaning_value
#print axioms ShielddSecurity.CapturedRegistryPointDomain75.meaning_value
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryPointDomain75.point_cast_equal
#print axioms ShielddSecurity.CapturedRegistryPointDomain75.point_cast_equal
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryPointDomain75.field_guards
#print axioms ShielddSecurity.CapturedRegistryPointDomain75.field_guards
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryPointDomain75.prepared_role
#print axioms ShielddSecurity.CapturedRegistryPointDomain75.prepared_role
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryPointDomain75.registry_coordinate_guards
#print axioms ShielddSecurity.CapturedRegistryPointDomain75.registry_coordinate_guards
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryPointDomain75.legal_registry_global104
#print axioms ShielddSecurity.CapturedRegistryPointDomain75.legal_registry_global104
