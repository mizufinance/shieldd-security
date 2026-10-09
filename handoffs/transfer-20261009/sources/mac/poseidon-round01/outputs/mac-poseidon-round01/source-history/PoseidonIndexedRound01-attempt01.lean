import ShielddSecurity.Poseidon
import ShielddSecurity.CompilerIndexed01
set_option maxHeartbeats 500000
namespace ShielddSecurity.PoseidonIndexedRound01
open Compiler CompilerIndexed01 Poseidon

structure FifthHint where
  square fourth auxiliary : Linear
  first second minus plus : Nat

def checkFifth (p copy : Nat) (rows : Array Row) (input output : Linear) (hint : FifthHint) : Bool :=
  checkUnoutlinedAt p copy rows hint.first ⟨input,hint.square⟩ &&
  checkUnoutlinedAt p copy rows hint.second ⟨hint.square,hint.fourth⟩ &&
  checkUnoutlinedAt p copy rows hint.minus ⟨subtract hint.fourth input,hint.auxiliary⟩ &&
  checkUnoutlinedAt p copy rows hint.plus ⟨hint.fourth++input,hint.auxiliary++scaleLinear 4 output⟩

theorem checkFifth_sound (p copy : Nat) (rows : Array Row) (input output : Linear) (hint : FifthHint)
    (checked : checkFifth p copy rows input output hint=true) :
    FifthCertificate p (unoutlineRows copy rows.toList) input output := by
  simp only [checkFifth,Bool.and_eq_true] at checked
  exact .arithmetic hint.square hint.fourth hint.auxiliary
    (checkUnoutlinedAt_sound p copy rows hint.first _ checked.1.1.1)
    (checkUnoutlinedAt_sound p copy rows hint.second _ checked.1.1.2)
    (checkUnoutlinedAt_sound p copy rows hint.minus _ checked.1.2)
    (checkUnoutlinedAt_sound p copy rows hint.plus _ checked.2)

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
end ShielddSecurity.PoseidonIndexedRound01
set_option pp.all true in
#check @ShielddSecurity.PoseidonIndexedRound01.checkFifth_sound
#print axioms ShielddSecurity.PoseidonIndexedRound01.checkFifth_sound
set_option pp.all true in
#check @ShielddSecurity.PoseidonIndexedRound01.checkRound_sound
#print axioms ShielddSecurity.PoseidonIndexedRound01.checkRound_sound
