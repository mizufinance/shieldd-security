import ShielddSecurity.FixedWindowJoin488
import ShielddSecurity.AuthorizationFixedTables490
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.FixedWindowMeaning491
open ConcreteJubjubField01 FixedSelectorAdapter480

def Matches (e : FixedWindowJoin488.Entry) : Prop :=
  e.selector.bx=(AuthorizationFixedTables490.table e.index).1.bx ∧
  e.selector.by_=(AuthorizationFixedTables490.table e.index).1.by_ ∧
  e.selector.tx=(AuthorizationFixedTables490.table e.index).1.tx ∧
  e.selector.ty=(AuthorizationFixedTables490.table e.index).1.ty ∧
  e.selector.ux=(AuthorizationFixedTables490.table e.index).1.ux ∧
  e.selector.uy=(AuthorizationFixedTables490.table e.index).1.uy
noncomputable instance matchesDecidable (e : FixedWindowJoin488.Entry) : Decidable (Matches e) := by
  unfold Matches
  infer_instance
noncomputable def check (e : FixedWindowJoin488.Entry) : Bool := decide (Matches e)

theorem points (e : FixedWindowJoin488.Entry) (checked : check e=true) :
    (base e.selector : Group.Point F)=base (AuthorizationFixedTables490.table e.index).1 ∧
    (twice e.selector : Group.Point F)=twice (AuthorizationFixedTables490.table e.index).1 ∧
    (triple e.selector : Group.Point F)=triple (AuthorizationFixedTables490.table e.index).1 := by
  have matched : Matches e := of_decide_eq_true checked
  rcases matched with ⟨bx,by_,tx,ty,ux,uy⟩
  simp only [base,twice,triple,bx,by_,tx,ty,ux,uy,and_self]
end ShielddSecurity.FixedWindowMeaning491

set_option pp.all true in
#check @ShielddSecurity.FixedWindowMeaning491.Matches
#print axioms ShielddSecurity.FixedWindowMeaning491.Matches

set_option pp.all true in
#check @ShielddSecurity.FixedWindowMeaning491.check
#print axioms ShielddSecurity.FixedWindowMeaning491.check

set_option pp.all true in
#check @ShielddSecurity.FixedWindowMeaning491.points
#print axioms ShielddSecurity.FixedWindowMeaning491.points
