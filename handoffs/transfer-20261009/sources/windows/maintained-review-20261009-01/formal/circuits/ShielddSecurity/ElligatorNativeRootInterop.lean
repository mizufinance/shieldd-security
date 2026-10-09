import ShielddSecurity.ElligatorNativeProgram

set_option maxHeartbeats 250000
set_option maxRecDepth 2048

namespace ShielddSecurity.ElligatorNativeRootInterop

variable {F : Type} [Field F] [CharP F Scalar.modulus]

/-- Two independently pinned sound/complete square-root interfaces agree on
existence. Their chosen raw roots may differ. -/
theorem choice_agreement (left right : ElligatorNativeRoots.SqrtAPI F) (value : F) :
    ElligatorNativeRoots.choice left value = ElligatorNativeRoots.choice right value := by
  have equivalent : ElligatorNativeRoots.choice left value = true ↔
      ElligatorNativeRoots.choice right value = true :=
    (left.complete value).trans (right.complete value).symm
  cases chosenLeft : ElligatorNativeRoots.choice left value <;>
    cases chosenRight : ElligatorNativeRoots.choice right value
  · rfl
  · have impossible : (false : Bool) = true := by
      simpa only [chosenLeft] using equivalent.mpr chosenRight
    cases impossible
  · have impossible : (false : Bool) = true := by
      simpa only [chosenRight] using equivalent.mp chosenLeft
    cases impossible
  · rfl

/-- Local sign normalization makes independent square-root APIs agree. The
first cubic's nonzero fact is derived by the owned map algebra at instantiation;
there is no requested raw root, parity, or generated point in the premises. -/
theorem normalized_root_agreement [Fintype F]
    (codec : TransferReduction.CanonicalField F)
    (left right : ElligatorNativeRoots.SqrtAPI F) (odd : ringChar F ≠ 2)
    (z u first : F) (zNonzero : z ≠ 0)
    (euler : z ^ (Fintype.card F / 2) = -1) (firstNonzero : first ≠ 0) :
    ElligatorNativeParity.normalizeRoot codec (ElligatorNativeRoots.choice left first)
      (ElligatorNativeRoots.rootValue left (ElligatorNativeRoots.selectedValue left z u first)) =
    ElligatorNativeParity.normalizeRoot codec (ElligatorNativeRoots.choice right first)
      (ElligatorNativeRoots.rootValue right (ElligatorNativeRoots.selectedValue right z u first)) := by
  have sameChoice := choice_agreement left right first
  have leftNormalized := ElligatorNativeParity.selected_normalization codec
    (ElligatorNativeRoots.choice left first) first (z*u*u*first)
    (ElligatorNativeRoots.rootValue left (ElligatorNativeRoots.selectedValue left z u first))
    firstNonzero (ElligatorNativeRoots.computed_roots left odd z u first zNonzero euler).2
  have rightNormalized := ElligatorNativeParity.selected_normalization codec
    (ElligatorNativeRoots.choice right first) first (z*u*u*first)
    (ElligatorNativeRoots.rootValue right (ElligatorNativeRoots.selectedValue right z u first))
    firstNonzero (ElligatorNativeRoots.computed_roots right odd z u first zNonzero euler).2
  apply ElligatorNative.codec_root_unique codec
  · rw [leftNormalized.1,rightNormalized.1,sameChoice]
  · rw [leftNormalized.2,rightNormalized.2,sameChoice]

variable [DecidableEq F]

/-- The complete owned rational map and three doubles preserve the API-independent
normalized point. Global native square-root contracts suffice; equal raw return
values from Commonware Scalar and SDK Fq are not assumed. -/
theorem generator_agreement [Fintype F] (codec : TransferReduction.CanonicalField F)
    (left right : ElligatorNativeRoots.SqrtAPI F) (odd : ringChar F ≠ 2)
    (fiveNonzero : (5 : F) ≠ 0) (fiveEuler : (5 : F) ^ (Fintype.card F / 2) = -1)
    (c1 c2 k d u : F) (firstNonzero : ElligatorNativeProgram.firstCubic c1 c2 u ≠ 0) :
    ElligatorNativeProgram.generatorValue codec left c1 c2 k d u =
      ElligatorNativeProgram.generatorValue codec right c1 c2 k d u := by
  dsimp only [ElligatorNativeProgram.generatorValue]
  rw [normalized_root_agreement codec left right odd 5 u
    (ElligatorNativeProgram.firstCubic c1 c2 u) fiveNonzero fiveEuler firstNonzero]
  rw [choice_agreement left right (ElligatorNativeProgram.firstCubic c1 c2 u)]

/-- Both source option programs return the same point from separate functional
ABIs. Availability is proved for each API; fallback failure is not assumed away. -/
theorem source_program_agreement [Fintype F]
    (codec : TransferReduction.CanonicalField F) (left right : ElligatorNativeRoots.SqrtAPI F)
    (odd : ringChar F ≠ 2) (fiveNonzero : (5 : F) ≠ 0)
    (fiveEuler : (5 : F) ^ (Fintype.card F / 2) = -1)
    (c1 c2 k d u : F) (firstNonzero : ElligatorNativeProgram.firstCubic c1 c2 u ≠ 0) :
    ElligatorNativeProgram.sourceProgram codec left c1 c2 k d u =
      ElligatorNativeProgram.sourceProgram codec right c1 c2 k d u := by
  rw [ElligatorNativeProgram.source_defined codec left odd fiveNonzero fiveEuler,
    ElligatorNativeProgram.source_defined codec right odd fiveNonzero fiveEuler]
  exact congrArg some (generator_agreement codec left right odd fiveNonzero fiveEuler
    c1 c2 k d u firstNonzero)

set_option pp.all true in
#check @choice_agreement
#print axioms choice_agreement
set_option pp.all true in
#check @normalized_root_agreement
#print axioms normalized_root_agreement
set_option pp.all true in
#check @generator_agreement
#print axioms generator_agreement
set_option pp.all true in
#check @source_program_agreement
#print axioms source_program_agreement

end ShielddSecurity.ElligatorNativeRootInterop
