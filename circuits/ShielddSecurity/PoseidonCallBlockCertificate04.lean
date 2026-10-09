import ShielddSecurity.PoseidonCallBlockComposition04
namespace ShielddSecurity.PoseidonCallBlockCertificate04
open Compiler CompilerCompletion
variable {F : Type} [Field F]
structure Certificate (p copy floor ceiling : Nat) (steps : List Step) (rows : List Row) : Prop where
  ordered : Topological [0,copy] [] steps
  support : ∀ row∈emitted steps,∀ term∈row.a++row.b,term.1<ceiling
  writes : ∀ column∈PoseidonCompletion.writes steps,floor≤column
  coverage : ∀ actual∈rows,∃ expected∈emitted steps,
    canonical p (unoutline copy actual.a)=canonical p expected.a ∧ canonical p (unoutline copy actual.b)=canonical p expected.b
  legal : ∀ base : Nat → F,Legal base steps

theorem append (p copy firstFloor firstCeiling secondFloor secondCeiling : Nat)
    (first second : List Step) (firstRows secondRows : List Row)
    (firstCertificate : Certificate (F:=F) p copy firstFloor firstCeiling first firstRows)
    (secondCertificate : Certificate (F:=F) p copy secondFloor secondCeiling second secondRows)
    (fresh : firstCeiling≤secondFloor) (floors : firstFloor≤secondFloor) (ceilings : firstCeiling≤secondCeiling) :
    Certificate (F:=F) p copy firstFloor secondCeiling (first++second) (firstRows++secondRows) := by
  constructor
  · exact PoseidonCallComposition04.topological_append_by_floor [0,copy] first second secondFloor firstCertificate.ordered secondCertificate.ordered
      (by intro row member term present
          exact Nat.lt_of_lt_of_le (firstCertificate.support row member term present) fresh) secondCertificate.writes
  · exact PoseidonCallBlockComposition04.support_append secondCeiling first second
      (by intro row member term present
          exact Nat.lt_of_lt_of_le (firstCertificate.support row member term present) ceilings) secondCertificate.support
  · exact PoseidonCallBlockComposition04.writes_lower_append firstFloor first second firstCertificate.writes
      (by intro column member
          exact Nat.le_trans floors (secondCertificate.writes column member))
  · exact PoseidonCallComposition04.reverse_append p copy firstRows secondRows first second firstCertificate.coverage secondCertificate.coverage
  · intro base
    exact PoseidonCallComposition04.legal_append base first second (firstCertificate.legal base) (secondCertificate.legal (run base first))
end ShielddSecurity.PoseidonCallBlockCertificate04
set_option pp.all true in
#check @ShielddSecurity.PoseidonCallBlockCertificate04.append
#print axioms ShielddSecurity.PoseidonCallBlockCertificate04.append
