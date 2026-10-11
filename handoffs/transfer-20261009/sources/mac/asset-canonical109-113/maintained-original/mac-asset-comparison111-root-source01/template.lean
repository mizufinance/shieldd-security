import ShielddSecurity.AssetComparison110Numeric
import ShielddSecurity.AssetComparison110Rows00
import ShielddSecurity.AssetComparison110Rows01
import ShielddSecurity.AssetComparison110Rows02
import ShielddSecurity.AssetComparison110Rows03
import ShielddSecurity.AssetComparison110Rows04
import ShielddSecurity.AssetComparison110Rows05
import ShielddSecurity.AssetComparison110Rows06
import ShielddSecurity.AssetComparison110Rows07
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AssetComparison111
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
    Satisfies (fun column => rho (AssetComparison110.rename column)) CapturedValueComparison105.actualRows := by
  apply (CompilerColumnRenaming05.satisfies_rows AssetComparison110.rename rho CapturedValueComparison105.actualRows).mp
  change Satisfies rho (CompilerColumnRenaming05.rows AssetComparison110.rename (CapturedValueComparison102Pilot.actualRows++(CapturedValueComparison104C01.actualRows++(CapturedValueComparison104C02.actualRows++(CapturedValueComparison104C03.actualRows++(CapturedValueComparison104C04.actualRows++(CapturedValueComparison104C05.actualRows++(CapturedValueComparison104C06.actualRows++(CapturedValueComparison104C07.actualRows)))))))))
  simp only [CompilerColumnRenaming05.rows,List.map_append]
  change Satisfies rho (AssetComparison110Rows00.actualRows++(AssetComparison110Rows01.actualRows++(AssetComparison110Rows02.actualRows++(AssetComparison110Rows03.actualRows++(AssetComparison110Rows04.actualRows++(AssetComparison110Rows05.actualRows++(AssetComparison110Rows06.actualRows++(AssetComparison110Rows07.actualRows))))))))
  apply sat_append
  · exact AssetComparison110Rows00.selected_satisfies rho arithmetic
  apply sat_append
  · exact AssetComparison110Rows01.selected_satisfies rho arithmetic
  apply sat_append
  · exact AssetComparison110Rows02.selected_satisfies rho arithmetic
  apply sat_append
  · exact AssetComparison110Rows03.selected_satisfies rho arithmetic
  apply sat_append
  · exact AssetComparison110Rows04.selected_satisfies rho arithmetic
  apply sat_append
  · exact AssetComparison110Rows05.selected_satisfies rho arithmetic
  apply sat_append
  · exact AssetComparison110Rows06.selected_satisfies rho arithmetic
  exact AssetComparison110Rows07.selected_satisfies rho arithmetic
variable [CharP F p]
theorem canonical_value (rho : Nat → F) (n : Nat) (bound : n<p) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (values : ∀ index<255,rho (471+index)=BinaryComparison100.bit (F:=F)
      (CapturedValueComparison106.bitAt n (216+index))) : 1-rho 725+rho 33260=1 := by
  have seed : ∀ index<255,(fun column => rho (AssetComparison110.rename column)) (216+index)=
      BinaryComparison100.bit (F:=F) (CapturedValueComparison106.bitAt n (216+index)) := by
    intro index before
    have renamed : AssetComparison110.rename (216+index)=471+index := by
      unfold AssetComparison110.rename
      rw [if_pos (show 216≤216+index ∧ 216+index<471 by omega)]
      omega
    change rho (AssetComparison110.rename (216+index))=_
    rw [renamed]
    exact values index before
  have linked : (fun column => rho (AssetComparison110.rename column)) copy=1 := by
    simpa only [AssetComparison110.copy_fixed] using one
  have result:=AssetComparison110.selected_numeric (fun column => rho (AssetComparison110.rename column)) n bound linked
    (pullback_satisfies rho arithmetic) seed
  have last : AssetComparison110.rename 470=725 := by decide
  have pivot : AssetComparison110.rename 32752=33260 := by decide
  simpa only [last,pivot] using result
end ShielddSecurity.AssetComparison111
