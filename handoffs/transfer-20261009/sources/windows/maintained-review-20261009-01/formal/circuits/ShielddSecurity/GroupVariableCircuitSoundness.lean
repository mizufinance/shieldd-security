import ShielddSecurity.GroupVariableCircuitNative

set_option maxHeartbeats 150000

namespace ShielddSecurity.GroupVariableCircuitSoundness

open GroupFixedCircuitCompletion GroupVariableCircuitCompletion

variable {F J : Type} [Field F] [AddCommGroup J]

/-- Each actual local proof must derive this formula from arbitrary satisfying
captured rows. A constructor formula does not discharge this obligation. -/
def LocalSound (d : F) (copy : Nat) (tables : Tables) (program : Program) : Prop :=
  ∀ rho : Nat → F, rho 0 = 1 → rho copy = rho 0 →
    Group.OnCurve d (point rho program.input) → Curved d tables rho →
    eval rho program.low = (if program.lowBit then 1 else 0) →
    eval rho program.high = (if program.highBit then 1 else 0) →
    Satisfies rho program.rows →
    point rho program.output = Group.affineAdd d
      (Group.affineAdd d (Group.affineAdd d (point rho program.input) (point rho program.input))
        (Group.affineAdd d (point rho program.input) (point rho program.input)))
      (Group.windowPoint (eval rho program.low) (eval rho program.high)
        (point rho tables.base) (point rho tables.twice) (point rho tables.triple))

/-- A single arbitrary assignment is used for every window. All local sound
proofs, source adjacency, bit interpretations and native table meanings remain
explicit obligations for the captured sequence adapter. -/
theorem checked_native (d : F) (copy : Nat) (model : Group.StandardCurveModel J d)
    (base acc : J) (rho : Nat → F) (tables : Tables) (programs : List Program)
    (input : Linear × Linear)
    (formulas : ∀ program ∈ programs, LocalSound d copy tables program)
    (alignment : Aligned input programs)
    (one : rho 0 = 1) (linked : rho copy = rho 0)
    (incoming : point rho input = model.coordinates acc)
    (baseTable : point rho tables.base = model.coordinates base)
    (twiceTable : point rho tables.twice = model.coordinates (2 • base))
    (tripleTable : point rho tables.triple = model.coordinates (3 • base))
    (bits : ∀ program ∈ programs,
      eval rho program.low = (if program.lowBit then 1 else 0) ∧
      eval rho program.high = (if program.highBit then 1 else 0))
    (satisfied : Satisfies rho (rows programs)) :
    point rho (output input programs) =
      model.coordinates (GroupVariableCircuitNative.nativeValue base programs acc) := by
  induction programs generalizing acc input with
  | nil =>
      simpa only [output,GroupVariableCircuitNative.nativeValue,
        GroupVariableCircuitNative.pairs,List.map_nil,List.foldl_nil] using incoming
  | cons program tail ih =>
      have current : point rho program.input = model.coordinates acc := by
        rw [alignment.1]
        exact incoming
      have curved : Curved d tables rho := by
        unfold Curved
        rw [baseTable,twiceTable,tripleTable]
        exact ⟨model.onCurve base,model.onCurve (2 • base),model.onCurve (3 • base)⟩
      have currentCurve : Group.OnCurve d (point rho program.input) := by
        rw [current]
        exact model.onCurve acc
      have currentBits := bits program List.mem_cons_self
      have localRows : Satisfies rho program.rows := by
        intro row member
        exact satisfied row (List.mem_append_left _ member)
      have formulaResult := formulas program List.mem_cons_self rho one linked
        currentCurve curved currentBits.1 currentBits.2 localRows
      rw [current,currentBits.1,currentBits.2,baseTable,twiceTable,tripleTable] at formulaResult
      have next := formulaResult.trans (GroupVariableCircuitNative.affine_window_native d model
        base acc program.lowBit program.highBit)
      have later := ih (4 • acc + (program.lowBit.toNat + 2 * program.highBit.toNat) • base)
        program.output
        (by intro later member; exact formulas later (List.mem_cons_of_mem _ member))
        alignment.2 next
        (by intro later member; exact bits later (List.mem_cons_of_mem _ member))
        (by intro row member; exact satisfied row (List.mem_append_right _ member))
      simpa only [output,GroupVariableCircuitNative.nativeValue,
        GroupVariableCircuitNative.pairs,List.map_cons,List.foldl_cons,
        GroupNativeMultiply.pairDigit] using later

set_option pp.all true in
#check @checked_native
#print axioms checked_native

end ShielddSecurity.GroupVariableCircuitSoundness
