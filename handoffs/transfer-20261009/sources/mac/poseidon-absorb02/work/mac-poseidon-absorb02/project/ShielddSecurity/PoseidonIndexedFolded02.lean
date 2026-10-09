import ShielddSecurity.PoseidonIndexedRound01
set_option maxHeartbeats 500000
namespace ShielddSecurity.PoseidonIndexedFolded02
open Compiler CompilerIndexed01 Poseidon

/-- Constant-native fifth powers emit no arithmetic rows. Arithmetic branches
retain the exact four actual indexed rows from the original decoder. -/
inductive FifthHint where
  | constant (coefficient : Int)
  | arithmetic (hint : PoseidonIndexedRound01.FifthHint)

def checkFifth (p copy : Nat) (rows : Array Row) (input output : Linear) : FifthHint → Bool
  | .constant coefficient =>
    decide (canonical p input=canonical p [(0,coefficient)]) &&
    decide (canonical p output=canonical p [(0,coefficient^5)])
  | .arithmetic hint => PoseidonIndexedRound01.checkFifth p copy rows input output hint

theorem checkFifth_sound (p copy : Nat) (rows : Array Row) (input output : Linear) (hint : FifthHint)
    (checked : checkFifth p copy rows input output hint=true) :
    FifthCertificate p (unoutlineRows copy rows.toList) input output := by
  cases hint with
  | constant coefficient =>
    simp only [checkFifth,Bool.and_eq_true] at checked
    exact .constant coefficient (of_decide_eq_true checked.1) (of_decide_eq_true checked.2)
  | arithmetic hint =>
    exact PoseidonIndexedRound01.checkFifth_sound p copy rows input output hint checked

def checkColumn {width : Nat} (p copy : Nat) (rows : Array Row) (parameters : Parameters Int width)
    (index : Nat) (before shifted transformed : State Linear width) (hints : Fin width → FifthHint)
    (column : Fin width) : Bool :=
  decide (canonical p (shifted column)=canonical p (before column++[(0,parameters.ark index column)])) &&
  if nonlinear index column.val then checkFifth p copy rows (shifted column) (transformed column) (hints column)
  else decide (canonical p (transformed column)=canonical p (shifted column))

def checkRound {width : Nat} (p copy : Nat) (rows : Array Row) (parameters : Parameters Int width)
    (index : Nat) (before shifted transformed after : State Linear width) (hints : Fin width → FifthHint) : Bool :=
  (List.finRange width).all (checkColumn p copy rows parameters index before shifted transformed hints) &&
  (List.finRange width).all (fun row => decide (canonical p (after row)=canonical p (mixLinear parameters.mds transformed row)))

theorem checkRound_sound {width : Nat} (p copy : Nat) (rows : Array Row) (parameters : Parameters Int width)
    (index : Nat) (before shifted transformed after : State Linear width) (hints : Fin width → FifthHint)
    (checked : checkRound p copy rows parameters index before shifted transformed after hints=true) :
    RoundCertificate p (unoutlineRows copy rows.toList) parameters index before shifted transformed after := by
  simp only [checkRound,Bool.and_eq_true] at checked
  have columnCheck (column : Fin width) := List.all_eq_true.mp checked.1 column (List.mem_finRange column)
  constructor
  · intro column
    have result := columnCheck column
    simp only [checkColumn,Bool.and_eq_true] at result
    exact of_decide_eq_true result.1
  · intro column nonlinearHere
    have result := columnCheck column
    simp only [checkColumn,Bool.and_eq_true,nonlinearHere,if_true] at result
    exact checkFifth_sound p copy rows _ _ (hints column) result.2
  · intro column linearHere
    have result := columnCheck column
    simp only [checkColumn,Bool.and_eq_true,linearHere,if_false] at result
    exact of_decide_eq_true result.2
  · intro row
    exact of_decide_eq_true (List.all_eq_true.mp checked.2 row (List.mem_finRange row))
end ShielddSecurity.PoseidonIndexedFolded02
set_option pp.all true in
#check @ShielddSecurity.PoseidonIndexedFolded02.checkFifth_sound
#print axioms ShielddSecurity.PoseidonIndexedFolded02.checkFifth_sound
set_option pp.all true in
#check @ShielddSecurity.PoseidonIndexedFolded02.checkRound_sound
#print axioms ShielddSecurity.PoseidonIndexedFolded02.checkRound_sound
