import ShielddSecurity.FixedWindowJoin488
import ShielddSecurity.BalanceBlindingTables673
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceBlindingMeaning674
open ConcreteJubjubField01 FixedSelectorAdapter480

def Matches (e : FixedWindowJoin488.Entry) : Prop :=
  e.selector.bx=(BalanceBlindingTables673.table e.index).1.bx ∧
  e.selector.by_=(BalanceBlindingTables673.table e.index).1.by_ ∧
  e.selector.tx=(BalanceBlindingTables673.table e.index).1.tx ∧
  e.selector.ty=(BalanceBlindingTables673.table e.index).1.ty ∧
  e.selector.ux=(BalanceBlindingTables673.table e.index).1.ux ∧
  e.selector.uy=(BalanceBlindingTables673.table e.index).1.uy
noncomputable instance matchesDecidable (e : FixedWindowJoin488.Entry) : Decidable (Matches e) := by
  unfold Matches
  infer_instance
noncomputable def check (e : FixedWindowJoin488.Entry) : Bool := decide (Matches e)

theorem points (e : FixedWindowJoin488.Entry) (checked : check e=true) :
    (base e.selector : Group.Point F)=base (BalanceBlindingTables673.table e.index).1 ∧
    (twice e.selector : Group.Point F)=twice (BalanceBlindingTables673.table e.index).1 ∧
    (triple e.selector : Group.Point F)=triple (BalanceBlindingTables673.table e.index).1 := by
  have matched : Matches e := of_decide_eq_true checked
  rcases matched with ⟨bx,by_,tx,ty,ux,uy⟩
  simp only [base,twice,triple,bx,by_,tx,ty,ux,uy,and_self]
end ShielddSecurity.BalanceBlindingMeaning674

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingMeaning674.Matches
#print axioms ShielddSecurity.BalanceBlindingMeaning674.Matches

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingMeaning674.check
#print axioms ShielddSecurity.BalanceBlindingMeaning674.check

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingMeaning674.points
#print axioms ShielddSecurity.BalanceBlindingMeaning674.points
