import ShielddSecurity.GroupFixedTemplateTrace

set_option maxHeartbeats 100000

namespace ShielddSecurity.GroupFixedTemplateNativeSoundness

/-- Soundness applies to any assignment satisfying the actual program rows.
The native input, generator and bit interpretations remain explicit contracts.
It does not assume a constructed assignment or a proposed output coordinate. -/
theorem checked_native {F : Type} [Field F] {p : Nat} [CharP F p]
    {J : Type} [AddCommGroup J] (copy : Nat) (d : Int)
    (model : Group.StandardCurveModel J (d : F))
    (rho : Nat → F) (windows : List GroupFixedTemplateTrace.Window)
    (input : Linear × Linear) (base : Group.Point Int) (acc generator : J)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (d : F)) (imaginarySquare : imaginary*imaginary = -1)
    (inputMeaning : GroupFixedCircuitCompletion.point rho input = model.coordinates acc)
    (baseMeaning : GroupFixedWindowTemplate.castPoint base = model.coordinates generator)
    (aligned : GroupFixedTemplateTrace.Aligned input base windows)
    (checked : ∀ window ∈ windows, window.Checked p copy d ∧ window.TableChecked p)
    (rows : Satisfies rho
      (GroupFixedCircuitCompletion.rows (windows.map GroupFixedTemplateTrace.Window.program)))
    (bits : ∀ window ∈ windows,
      eval rho window.program.low = (if window.program.lowBit then 1 else 0) ∧
      eval rho window.program.high = (if window.program.highBit then 1 else 0)) :
    GroupFixedCircuitCompletion.point rho (GroupFixedTemplateTrace.endpoint input windows) =
      model.coordinates (acc + TransferWindows.digitsValue
        ((windows.map (fun window => window.witness rho)).map GroupFixedWindows.fixedDigit) • generator) := by
  have trace := GroupFixedTemplateTrace.checked_trace copy d rho one four imaginary
    nonSquare imaginarySquare windows input base aligned checked rows bits
  rw [inputMeaning,baseMeaning] at trace
  have native := GroupFixedWindows.fixed_trace_value_coordinates (d : F) imaginary model
    nonSquare imaginarySquare (windows.map (fun window => window.witness rho)) acc generator trace
  exact (GroupFixedTemplateTrace.endpoint_trace rho windows input).trans
    (by rw [inputMeaning]; exact native)

set_option pp.all true in
#check @checked_native
#print axioms checked_native

end ShielddSecurity.GroupFixedTemplateNativeSoundness
