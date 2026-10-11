import ShielddSecurity.AssetComparison110Numeric
import ShielddSecurity.NextComparison115Rows00
import ShielddSecurity.NextComparison115Rows01
import ShielddSecurity.NextComparison115Rows02
import ShielddSecurity.NextComparison115Rows03
import ShielddSecurity.NextComparison115Rows04
import ShielddSecurity.NextComparison115Rows05
import ShielddSecurity.NextComparison115Rows06
import ShielddSecurity.NextComparison115Rows07
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.NextComparison116
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F]
private theorem sat_append (rho : Nat → F) (left right : List Row)
    (a : Satisfies rho left) (b : Satisfies rho right) : Satisfies rho (left++right) := by
  intro row member
  rcases List.mem_append.mp member with member|member
  · exact a row member
  · exact b row member
theorem pullback_satisfies (rho : Nat → F)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    Satisfies (fun column => rho (NextComparison115.rename column)) CapturedValueComparison105.actualRows := by
  apply (CompilerColumnRenaming05.satisfies_rows NextComparison115.rename rho CapturedValueComparison105.actualRows).mp
  change Satisfies rho (CompilerColumnRenaming05.rows NextComparison115.rename (CapturedValueComparison102Pilot.actualRows++(CapturedValueComparison104C01.actualRows++(CapturedValueComparison104C02.actualRows++(CapturedValueComparison104C03.actualRows++(CapturedValueComparison104C04.actualRows++(CapturedValueComparison104C05.actualRows++(CapturedValueComparison104C06.actualRows++(CapturedValueComparison104C07.actualRows)))))))))
  simp only [CompilerColumnRenaming05.rows,List.map_append]
  change Satisfies rho (NextComparison115Rows00.actualRows++(NextComparison115Rows01.actualRows++(NextComparison115Rows02.actualRows++(NextComparison115Rows03.actualRows++(NextComparison115Rows04.actualRows++(NextComparison115Rows05.actualRows++(NextComparison115Rows06.actualRows++(NextComparison115Rows07.actualRows))))))))
  apply sat_append
  · exact NextComparison115Rows00.selected_satisfies rho arithmetic
  apply sat_append
  · exact NextComparison115Rows01.selected_satisfies rho arithmetic
  apply sat_append
  · exact NextComparison115Rows02.selected_satisfies rho arithmetic
  apply sat_append
  · exact NextComparison115Rows03.selected_satisfies rho arithmetic
  apply sat_append
  · exact NextComparison115Rows04.selected_satisfies rho arithmetic
  apply sat_append
  · exact NextComparison115Rows05.selected_satisfies rho arithmetic
  apply sat_append
  · exact NextComparison115Rows06.selected_satisfies rho arithmetic
  exact NextComparison115Rows07.selected_satisfies rho arithmetic
variable [CharP F p]
theorem canonical_value (rho : Nat → F) (n : Nat) (bound : n<p) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (values : ∀ index<255,rho (726+index)=BinaryComparison100.bit (F:=F)
      (CapturedValueComparison106.bitAt n (216+index))) : 1-rho 980+rho 33768=1 := by
  have seed : ∀ index<255,(fun column => rho (NextComparison115.rename column)) (216+index)=
      BinaryComparison100.bit (F:=F) (CapturedValueComparison106.bitAt n (216+index)) := by
    intro index before
    have renamed : NextComparison115.rename (216+index)=726+index := by
      unfold NextComparison115.rename
      rw [if_pos (show 216≤216+index ∧ 216+index<726 by omega)]
      omega
    change rho (NextComparison115.rename (216+index))=_
    rw [renamed]
    exact values index before
  have linked : (fun column => rho (NextComparison115.rename column)) copy=1 := by
    simpa only [NextComparison115.copy_fixed] using one
  have result:=AssetComparison110.selected_numeric (fun column => rho (NextComparison115.rename column)) n bound linked
    (pullback_satisfies rho arithmetic) seed
  have last : NextComparison115.rename 470=980 := by decide
  have pivot : NextComparison115.rename 32752=33768 := by decide
  simpa only [last,pivot] using result
end ShielddSecurity.NextComparison116
