import ShielddSecurity.TransferRegistryUserCompletion

set_option maxHeartbeats 150000

/-! Inverse coverage of authenticated registry inputs. The semantic registry
predicate is consumed only in this reverse direction. The forward constructor
still computes the selected asset from independently legal registry inputs.
These statements neither construct circuit rows nor establish Rust refinement. -/
namespace ShielddSecurity.TransferRegistryDecomposition

open TransferCore TransferSem TransferRegistryUserCompletion

def recoverInputs (c : Crypto) (w : TransferSem.Witness)
    (legal : RegistrySem c w) (canonical : fieldsCanonical (registryFields w.registry)) :
    RegistryInputs c w where
  leaf := w.registry
  regulated := w.regulated
  gapAsset := w.asset
  detectionValid := legal.1
  ringValid := legal.2.1
  payloadValid := legal.2.2.1
  checkingValid := legal.2.2.2.1
  epochBounded := legal.2.2.2.2.1
  positionBounded := legal.2.2.2.2.2.1
  valueCanonical := legal.2.2.2.2.2.2.1
  nextValueCanonical := legal.2.2.2.2.2.2.2.2.1
  gapAssetCanonical := legal.2.2.2.2.2.2.2.1
  leafCanonical := canonical
  authenticated := legal.2.2.2.2.2.2.2.2.2.1
  activeAudit := by
    intro active
    have branch := legal.2.2.2.2.2.2.2.2.2.2
    rw [if_pos active] at branch
    exact branch.2
  strictGap := by
    intro inactive
    have branch := legal.2.2.2.2.2.2.2.2.2.2
    rw [if_neg (by simp [inactive])] at branch
    exact branch

theorem recovered_raw_fields (c : Crypto) (w : TransferSem.Witness)
    (legal : RegistrySem c w) (canonical : fieldsCanonical (registryFields w.registry)) :
    (recoverInputs c w legal canonical).leaf = w.registry ∧
      (recoverInputs c w legal canonical).regulated = w.regulated ∧
      (recoverInputs c w legal canonical).gapAsset = w.asset :=
  ⟨rfl, rfl, rfl⟩

theorem selected_asset_recovered (c : Crypto) (w : TransferSem.Witness)
    (legal : RegistrySem c w) (canonical : fieldsCanonical (registryFields w.registry)) :
    selectedAsset c w (recoverInputs c w legal canonical) = w.asset := by
  change (if w.regulated then w.registry.value else w.asset) = w.asset
  by_cases active : w.regulated = true
  · have branch := legal.2.2.2.2.2.2.2.2.2.2
    rw [if_pos active] at branch ⊢
    exact branch.1.symm
  · rw [if_neg active]

theorem full_record_reconstructed (c : Crypto) (w : TransferSem.Witness)
    (legal : RegistrySem c w) (canonical : fieldsCanonical (registryFields w.registry)) :
    constructRegistry c w (recoverInputs c w legal canonical) = w := by
  unfold constructRegistry
  rw [selected_asset_recovered c w legal canonical]

def recoverAt (c : Crypto) (base w : TransferSem.Witness)
    (anchor : w.assetAnchor = base.assetAnchor)
    (legal : RegistrySem c w) (canonical : fieldsCanonical (registryFields w.registry)) :
    RegistryInputs c base where
  leaf := w.registry
  regulated := w.regulated
  gapAsset := w.asset
  detectionValid := (recoverInputs c w legal canonical).detectionValid
  ringValid := (recoverInputs c w legal canonical).ringValid
  payloadValid := (recoverInputs c w legal canonical).payloadValid
  checkingValid := (recoverInputs c w legal canonical).checkingValid
  epochBounded := (recoverInputs c w legal canonical).epochBounded
  positionBounded := (recoverInputs c w legal canonical).positionBounded
  valueCanonical := (recoverInputs c w legal canonical).valueCanonical
  nextValueCanonical := (recoverInputs c w legal canonical).nextValueCanonical
  gapAssetCanonical := (recoverInputs c w legal canonical).gapAssetCanonical
  leafCanonical := canonical
  authenticated := (recoverInputs c w legal canonical).authenticated.trans anchor
  activeAudit := (recoverInputs c w legal canonical).activeAudit
  strictGap := (recoverInputs c w legal canonical).strictGap

theorem recovered_at_selected_asset (c : Crypto) (base w : TransferSem.Witness)
    (anchor : w.assetAnchor = base.assetAnchor)
    (legal : RegistrySem c w) (canonical : fieldsCanonical (registryFields w.registry)) :
    selectedAsset c base (recoverAt c base w anchor legal canonical) = w.asset :=
  selected_asset_recovered c w legal canonical

theorem recovered_at_owned_fields (c : Crypto) (base w : TransferSem.Witness)
    (anchor : w.assetAnchor = base.assetAnchor)
    (legal : RegistrySem c w) (canonical : fieldsCanonical (registryFields w.registry)) :
    let result := constructRegistry c base (recoverAt c base w anchor legal canonical)
    result.registry = w.registry ∧ result.regulated = w.regulated ∧ result.asset = w.asset :=
  ⟨rfl, rfl, recovered_at_selected_asset c base w anchor legal canonical⟩

set_option pp.all true in
#check @recovered_raw_fields
#print axioms recovered_raw_fields
set_option pp.all true in
#check @selected_asset_recovered
#print axioms selected_asset_recovered
set_option pp.all true in
#check @full_record_reconstructed
#print axioms full_record_reconstructed
set_option pp.all true in
#check @recovered_at_selected_asset
#print axioms recovered_at_selected_asset
set_option pp.all true in
#check @recovered_at_owned_fields
#print axioms recovered_at_owned_fields

end ShielddSecurity.TransferRegistryDecomposition
