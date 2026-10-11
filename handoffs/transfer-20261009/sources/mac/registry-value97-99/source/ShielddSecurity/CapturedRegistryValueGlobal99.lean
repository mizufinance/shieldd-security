import ShielddSecurity.CapturedRegistryValueFrame98
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistryValueGlobal99
open CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F]
abbrev completed := CapturedRegistryValueFrame98.completed (F:=F)


set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryValueGlobal99.completed
#print axioms ShielddSecurity.CapturedRegistryValueGlobal99.completed
theorem claimed_seed (base : Nat → F) (n : Nat) (group : Fin 4) :
    CapturedFourSubgroupSeed89.Claimed (CapturedRegistryValueRange97.completed base n) group=
      CapturedFourSubgroupSeed89.Claimed base group := by
  have fourteen:=CapturedSubgroupFrame92.safe group 14 (by decide) (by decide)
  have fifteen:=CapturedSubgroupFrame92.safe group 15 (by decide) (by decide)
  change Group.Point.mk _ _=Group.Point.mk _ _
  rw [CapturedRegistryValueRange97.completed_outside base n _ (Or.inl (Nat.lt_trans fourteen.2.2.2.2.2 (by decide))),
    CapturedRegistryValueRange97.completed_outside base n _ (Or.inl (Nat.lt_trans fifteen.2.2.2.2.2 (by decide)))]


set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryValueGlobal99.claimed_seed
#print axioms ShielddSecurity.CapturedRegistryValueGlobal99.claimed_seed
theorem legal_registry_global420 [CharP F p] (c : TransferSem.Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.RegistrySem c w) (sinkMeaning : c.unregulatedRing=CapturedRegistryPointDomain75.sink)
    (base : Nat → F) (initial : Fin 4 → Group.Point F) (imaginary : F)
    (epoch : base 34=(w.registry.audit.epoch:F)) (position : base 135=(w.registry.position:F))
    (regulated : base 10=(if w.regulated then 1 else 0))
    (asset : base 6=(w.asset:F)) (registry : base 11=(w.registry.value:F))
    (px : base 35=(w.registry.audit.payload.x:F)) (py : base 36=(w.registry.audit.payload.y:F))
    (cx : base 42=(w.registry.audit.checking.x:F)) (cy : base 43=(w.registry.audit.checking.y:F))
    (zero : base 0=1)
    (binding : ∀ group,CapturedFourSubgroupSeed89.Claimed base group=
      CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) (initial group))
    (valid : ∀ group,Group.OnCurve (CapturedFirstSubgroup81.d:F) (initial group))
    (nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F)) (imaginarySquare : imaginary*imaginary=-1) :
    SatisfiesAt (completed base initial w.registry.value w.registry.audit.epoch w.registry.position)
      CapturedFullArithmetic52.rowAt 177954 ∧
    SatisfiesAt (completed base initial w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (177954+index)) 163 ∧
    SatisfiesAt (completed base initial w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (178118+index)) 1 ∧
    SatisfiesAt (completed base initial w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (178119+index)) 256 := by
  have low (column : Nat) (bound : column<216) :
      CapturedRegistryValueRange97.completed base w.registry.value column=base column :=
    CapturedRegistryValueRange97.completed_outside base _ column (Or.inl bound)
  have first:=CapturedGlobalSubgroup90.legal_registry_global163 c w legal sinkMeaning
    (CapturedRegistryValueRange97.completed base w.registry.value) initial imaginary
    ((low 34 (by decide)).trans epoch) ((low 135 (by decide)).trans position)
    ((low 10 (by decide)).trans regulated)
    ((low 35 (by decide)).trans px) ((low 36 (by decide)).trans py)
    ((low 42 (by decide)).trans cx) ((low 43 (by decide)).trans cy)
    ((low 0 (by decide)).trans zero)
    (fun group => (claimed_seed base w.registry.value group).trans (binding group))
    valid nonSquare imaginarySquare
  have assetRow:=CapturedRegulatedAsset96.legal_zero c w legal
    (CapturedRegistryValueRange97.completed base w.registry.value) initial
    ((low 6 (by decide)).trans asset) ((low 11 (by decide)).trans registry)
    ((low 10 (by decide)).trans regulated)
  exact ⟨first.1,first.2,assetRow,CapturedRegistryValueFrame98.legal_range c w legal base initial registry⟩


set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryValueGlobal99.legal_registry_global420
#print axioms ShielddSecurity.CapturedRegistryValueGlobal99.legal_registry_global420
def selectedIndex (index : Nat) : Nat :=
  if index<163 then 177954+index else if index<164 then 178118 else 178119+(index-164)


set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryValueGlobal99.selectedIndex
#print axioms ShielddSecurity.CapturedRegistryValueGlobal99.selectedIndex
theorem selected_complete (rho : Nat → F)
    (first : SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (177954+index)) 163)
    (asset : SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (178118+index)) 1)
    (rangeRows : SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (178119+index)) 256) :
    SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (selectedIndex index)) 420 := by
  intro index bound row found
  by_cases before : index<163
  · change CapturedFullRelation58.rowAt (if index<163 then 177954+index else if index<164 then 178118 else 178119+(index-164))=some row at found
    rw [if_pos before] at found
    exact first index before row found
  · by_cases assetIndex : index<164
    · have same : index=163 := by omega
      subst index
      change CapturedFullRelation58.rowAt 178118=some row at found
      exact asset 0 (by decide) row found
    · change CapturedFullRelation58.rowAt (if index<163 then 177954+index else if index<164 then 178118 else 178119+(index-164))=some row at found
      rw [if_neg before,if_neg assetIndex] at found
      exact rangeRows (index-164) (by omega) row found
end ShielddSecurity.CapturedRegistryValueGlobal99

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryValueGlobal99.selected_complete
#print axioms ShielddSecurity.CapturedRegistryValueGlobal99.selected_complete
