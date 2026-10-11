import ShielddSecurity.CompilerIndexedCoverage36
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CompilerArithmeticTransport41
open Compiler CompilerIndexed01 CompilerCertificateTransport
def p : Nat := 52435875175126190479447740508185965837690552500527637822603658699938581184513
def copy : Nat := 200692
variable {F : Type} [Field F] [CharP F p]
theorem four_ne_zero : (4:F)≠0 := by
  intro zero
  have divided := (CharP.cast_eq_zero_iff F p 4).mp zero
  have impossible : ¬p∣4 := by norm_num [p]
  exact impossible divided
theorem transfer (rho : Nat → F) (localRows fullRows : List Row)
    (checked : checkOriginalCoverage p 0 localRows.toArray fullRows.toArray (List.range localRows.length).toArray=true)
    (sat : Satisfies rho fullRows) : Satisfies rho localRows := by
  intro row member
  obtain ⟨expected,included,left,right⟩ := checked_inclusion p localRows.toArray fullRows.toArray _ checked row (by simpa using member)
  have square := sat expected (by simpa using included)
  change Square (eval rho row.a) (eval rho row.b)
  rw [canonical_equal rho row.a expected.a left,canonical_equal rho row.b expected.b right]
  exact square
end ShielddSecurity.CompilerArithmeticTransport41
set_option pp.all true in
#check @ShielddSecurity.CompilerArithmeticTransport41.p
#print axioms ShielddSecurity.CompilerArithmeticTransport41.p
set_option pp.all true in
#check @ShielddSecurity.CompilerArithmeticTransport41.copy
#print axioms ShielddSecurity.CompilerArithmeticTransport41.copy
set_option pp.all true in
#check @ShielddSecurity.CompilerArithmeticTransport41.four_ne_zero
#print axioms ShielddSecurity.CompilerArithmeticTransport41.four_ne_zero
set_option pp.all true in
#check @ShielddSecurity.CompilerArithmeticTransport41.transfer
#print axioms ShielddSecurity.CompilerArithmeticTransport41.transfer
