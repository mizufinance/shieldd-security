import ShielddSecurity.MapSeedValues724
import ShielddSecurity.MapWitnessFrame717
import ShielddSecurity.MapFunctionalFrame719
import ShielddSecurity.MapCofactorJoin714
import ShielddSecurity.BalanceCombined696
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapAssignmentValues720
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
attribute [local irreducible] model ConcreteCofactorModel01.model

noncomputable def assignment (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  BalanceCombined696.assignment (BalanceMapSeed703.seed original u) c w legal (BalanceMapPoint701.represented u)
    rkInitial authInitial initial senderInitial receiverInitial
attribute [local irreducible] assignment

theorem stable_value (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (column : Nat) (inside : MapWitnessLayout715.Inside column) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial column=BalanceMapSeed703.value u column := by
  have bounds := MapWitnessLayout715.bounds column inside
  unfold assignment BalanceCombined696.assignment
  rw [MapWitnessFrame717.blinding_frame _ c w legal rkInitial authInitial initial senderInitial receiverInitial column inside,
    BalanceMagnitudeTrace640.outside _ _ _ column (Or.inl (by omega))]
  exact BalanceMapSeed703.seed_value original u column (by
    simp only [MapWitnessLayout715.Inside,MapWitnessLayout715.values,List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)


set_option pp.all true in
#check @ShielddSecurity.MapAssignmentValues720.stable_value
#print axioms ShielddSecurity.MapAssignmentValues720.stable_value

theorem observed (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (out input : Nat)
    (inside : MapFunctionalFrame719.Region input) (f : F → F)
    (completion : ∀ (base : Nat → F) (c : Crypto) (w : TransferSem.Witness)
      (initial : Fin 4 → Group.Point F), HeaderRegisteredConstruction310.completed base c w initial out=
        f (RegisteredConstructorFrame309.prepared base c w input))
    (member : input∈BalanceMapSeed703.columns) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial out=
      f (BalanceMapSeed703.value u input) := by
  have bounds : 20934≤ input ∧ input<21199 := inside
  unfold assignment BalanceCombined696.assignment
  rw [MapFunctionalFrame719.blinding_frame out input inside f completion _ c w legal rkInitial authInitial initial senderInitial receiverInitial,
    BalanceMagnitudeTrace640.outside _ _ _ input (Or.inl (by omega)),
    BalanceMapSeed703.seed_value original u input member]

set_option pp.all true in
#check @ShielddSecurity.MapAssignmentValues720.observed
#print axioms ShielddSecurity.MapAssignmentValues720.observed

theorem choice_value (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 20935=
      if BalanceMapRoots700.choice u then 1 else 0 :=
  (observed original u c w legal rkInitial authInitial initial senderInitial receiverInitial 20935 20937
    (by change 20934≤20937 ∧ 20937<21199;decide)
    (fun value : F => ((representation.value value%2:Nat):F)) MapCompletionFlags718.choice_completed
    (by decide)).trans ((congrArg (fun value : F => ((representation.value value%2:Nat):F))
      (MapSeedValues724.selected u)).trans (MapCompletionFlags718.selected_parity u))

set_option pp.all true in
#check @ShielddSecurity.MapAssignmentValues720.choice_value
#print axioms ShielddSecurity.MapAssignmentValues720.choice_value

theorem zero_value (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 21193=BalanceMapPoint701.zero u :=
  (observed original u c w legal rkInitial authInitial initial senderInitial receiverInitial 21193 21193
    (by change 20934≤21193 ∧ 21193<21199;decide)
    MapCompletionFlags718.booleanize MapCompletionFlags718.zero_completed (by decide)).trans
    ((congrArg MapCompletionFlags718.booleanize (MapSeedValues724.zero u)).trans
      (MapCompletionFlags718.zero_booleanize u))

set_option pp.all true in
#check @ShielddSecurity.MapAssignmentValues720.zero_value
#print axioms ShielddSecurity.MapAssignmentValues720.zero_value

theorem copied (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial copy=1 := by
  unfold assignment BalanceCombined696.assignment
  exact BalanceBlindingBindings680.copied _ c w legal rkInitial authInitial initial senderInitial receiverInitial


set_option pp.all true in
#check @ShielddSecurity.MapAssignmentValues720.copied
#print axioms ShielddSecurity.MapAssignmentValues720.copied

theorem arithmetic (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) CapturedFullArithmetic52.rowAt 177954 := by
  unfold assignment BalanceCombined696.assignment
  exact BalanceBlindingBindings680.arithmetic _ c w legal rkInitial authInitial initial senderInitial receiverInitial


set_option pp.all true in
#check @ShielddSecurity.MapAssignmentValues720.arithmetic
#print axioms ShielddSecurity.MapAssignmentValues720.arithmetic

theorem values (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    MapCofactorJoin714.Values (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) u := by
  refine ⟨⟨copied original u c w legal rkInitial authInitial initial senderInitial receiverInitial,
    ?_,choice_value original u c w legal rkInitial authInitial initial senderInitial receiverInitial,
    ?_,zero_value original u c w legal rkInitial authInitial initial senderInitial receiverInitial,?_⟩,?_,?_,?_⟩
  · exact (stable_value original u c w legal rkInitial authInitial initial senderInitial receiverInitial 20934
      (by change 20934∈MapWitnessLayout715.values;decide)).trans (MapSeedValues724.initial u)
  · exact (stable_value original u c w legal rkInitial authInitial initial senderInitial receiverInitial 20937
      (by change 20937∈MapWitnessLayout715.values;decide)).trans (MapSeedValues724.selected u)
  · exact (stable_value original u c w legal rkInitial authInitial initial senderInitial receiverInitial 21194
      (by change 21194∈MapWitnessLayout715.values;decide)).trans (MapSeedValues724.inverse u)
  · exact (stable_value original u c w legal rkInitial authInitial initial senderInitial receiverInitial 21195
      (by change 21195∈MapWitnessLayout715.values;decide)).trans (MapSeedValues724.first u)
  · exact (stable_value original u c w legal rkInitial authInitial initial senderInitial receiverInitial 21196
      (by change 21196∈MapWitnessLayout715.values;decide)).trans (MapSeedValues724.second u)
  · exact (stable_value original u c w legal rkInitial authInitial initial senderInitial receiverInitial 21197
      (by change 21197∈MapWitnessLayout715.values;decide)).trans (MapSeedValues724.third u)


set_option pp.all true in
#check @ShielddSecurity.MapAssignmentValues720.values
#print axioms ShielddSecurity.MapAssignmentValues720.values

private theorem transported_coordinates {d e : F} (equal : d=e)
    (m : Group.StandardCurveModel curve.Point e) :
    (cast (congrArg (fun t : F => Group.StandardCurveModel curve.Point t) equal.symm) m).coordinates=m.coordinates := by
  cases equal
  rfl

theorem model_coordinates (point : curve.Point) : model.coordinates point=ConcreteCofactorModel01.model.coordinates point := by
  unfold model
  exact congrFun (transported_coordinates coefficient_eq ConcreteCofactorModel01.model) point


set_option pp.all true in
#check @ShielddSecurity.MapAssignmentValues720.model_coordinates
#print axioms ShielddSecurity.MapAssignmentValues720.model_coordinates

end ShielddSecurity.MapAssignmentValues720
