import ShielddSecurity.TierFlagBindings630
import ShielddSecurity.TierSelectors631
import ShielddSecurity.PayloadInputFrame566
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierBase632
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
attribute [local irreducible] SemanticWordFrame373.assignment model
noncomputable def payloadX : Linear := [(121566,1),(copy,49822839976625491399435002605169580882773999909559575334089637637825427273330)]
noncomputable def payloadY : Linear := [(121568,1),(copy,29108985603249989484651727880329493522712908252517904247459350893053326313050)]

theorem payload_selected (rho : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (one : rho copy=1) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (inputs : PayloadInputFrame566.Inputs rho w) :
    VariableWindowJoin443.point rho payloadX payloadY=SubgroupSeedCompletion203.fieldPoint (PayloadGroupDomain557.selected c w) := by
  change rho 200692=1 at one
  have x := TierSelectors631.payloadX_value rho arithmetic
  have y := TierSelectors631.payloadY_value rho arithmetic
  change VariableWindowJoin443.point rho payloadX payloadY=SubgroupSeedCompletion203.fieldPoint
    (if w.regulated then w.registry.audit.payload else CapturedRegistryPointDomain75.sink)
  simp only [CompilerArithmeticTransport41.copy,VariableWindowJoin443.point,payloadX,payloadY,eval,Int.cast_one,one_mul,add_zero,Int.cast_ofNat,one,x,y,
    inputs.flag,inputs.payloadX,inputs.payloadY,Int.cast_neg,neg_mul,mul_one]
  cases flag : w.regulated <;>
    simp only [Bool.false_eq_true,if_false,if_true,SubgroupSeedCompletion203.fieldPoint,CapturedRegistryPointDomain75.sink]
  · apply congrArg₂ Group.Point.mk <;> ring
  · apply congrArg₂ Group.Point.mk <;> ring

noncomputable def baseX (family : Fin 5) : Linear :=
  [[(121566,1),(142312,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(33790,1),(200692,17832230285398775523840151435063191920633280288053987250961356462684628833490)],[(121566,1),(154386,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(121566,1),(161679,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(121566,1),(168972,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)]].getD family.val []
noncomputable def baseY (family : Fin 5) : Linear :=
  [[(121568,1),(142314,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],[(33792,1),(200692,52236742954115892447572473178524297982305297140137344394933767595493156073169)],[(121568,1),(154388,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],[(121568,1),(161681,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],[(121568,1),(168974,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)]].getD family.val []

theorem coordinate_choice (payload detector shift payloadConstant detectorConstant : F)
    (chosen : Bool) (flag : F) (meaning : flag=if chosen then 1 else 0)
    (shifted : shift=flag*((detector-payload)+(detectorConstant-payloadConstant))) :
    payload+(shift+payloadConstant)=if chosen then detector+detectorConstant else payload+payloadConstant := by
  cases chosen <;> simp only [Bool.false_eq_true,if_false,if_true] at meaning ⊢ <;>
    rw [shifted,meaning] <;> ring

theorem selected (rho : Nat → F) (c : Crypto) (w : TransferSem.Witness) (family : Fin 5)
    (one : rho copy=1) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (payload : PayloadInputFrame566.Inputs rho w) (detection : DetectionInputFrame625.Inputs rho w)
    (flag : rho 108486=if flagged w then 1 else 0) :
    VariableWindowJoin443.point rho (baseX family) (baseY family)=
      SubgroupSeedCompletion203.fieldPoint (TierGroupDomain612.selected c w family) := by
  change rho 200692=1 at one
  have payloadPoint := payload_selected rho (DetectionGroupDomain611.baseCrypto c) w one arithmetic payload
  have detectionPoint := DetectionBase627.selected rho c w one arithmetic detection
  have px := congrArg Group.Point.x payloadPoint
  have py := congrArg Group.Point.y payloadPoint
  have dx := congrArg Group.Point.x detectionPoint
  have dy := congrArg Group.Point.y detectionPoint
  simp only [CompilerArithmeticTransport41.copy,VariableWindowJoin443.point,payloadX,payloadY,DetectionBase627.baseX,DetectionBase627.baseY,
    eval,Int.cast_one,one_mul,add_zero,Int.cast_ofNat,one,mul_one] at px py dx dy
  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ ∨ family=⟨2,by decide⟩ ∨
      family=⟨3,by decide⟩ ∨ family=⟨4,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl|rfl|rfl|rfl
  · have x := TierSelectors631.family0X_value rho arithmetic
    have y := TierSelectors631.family0Y_value rho arithmetic
    simp only [CompilerArithmeticTransport41.copy,eval,Int.cast_one,one_mul,add_zero,Int.cast_sub,Int.cast_neg,Int.cast_ofNat,neg_mul,one,mul_one] at x y
    have selectedX := coordinate_choice (rho 121566) (rho 33790) (rho 142312)
      (49822839976625491399435002605169580882773999909559575334089637637825427273330:F) (17832230285398775523840151435063191920633280288053987250961356462684628833490:F) (flagged w) (rho 108486) flag (by
        rw [x]
        ring)
    have selectedY := coordinate_choice (rho 121568) (rho 33792) (rho 142314)
      (29108985603249989484651727880329493522712908252517904247459350893053326313050:F) (52236742954115892447572473178524297982305297140137344394933767595493156073169:F) (flagged w) (rho 108486) flag (by
        rw [y]
        ring)
    rw [px,dx] at selectedX
    rw [py,dy] at selectedY
    cases chosen : flagged w <;>
      simp only [chosen,Bool.false_eq_true,if_false,if_true] at selectedX selectedY
    all_goals
      change Group.Point.mk _ _=SubgroupSeedCompletion203.fieldPoint
        (if (decide ((0:Nat)=1) || flagged w) then DetectionGroupDomain611.selected c w
          else PayloadGroupDomain557.selected (DetectionGroupDomain611.baseCrypto c) w)
      simp only [chosen,show decide ((0:Nat)=1)=false by decide,Bool.false_or,
        Bool.false_eq_true,if_false,if_true,SubgroupSeedCompletion203.fieldPoint]
      apply congrArg₂ Group.Point.mk
      · change eval rho [(121566,1),(142312,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)] = _
        have evaluated : eval rho [(121566,1),(142312,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)]=rho 121566+(rho 142312+(49822839976625491399435002605169580882773999909559575334089637637825427273330:F)) := by
          simp only [eval,Int.cast_one,one_mul,add_zero,Int.cast_ofNat,one,mul_one]
        exact evaluated.trans selectedX
      · change eval rho [(121568,1),(142314,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)] = _
        have evaluated : eval rho [(121568,1),(142314,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)]=rho 121568+(rho 142314+(29108985603249989484651727880329493522712908252517904247459350893053326313050:F)) := by
          simp only [eval,Int.cast_one,one_mul,add_zero,Int.cast_ofNat,one,mul_one]
        exact evaluated.trans selectedY
  · simpa only [baseX,baseY,List.getD,TierGroupDomain612.selected,TierGroupDomain612.useDetection,
      Fin.val_mk,decide_true,Bool.true_or,if_true] using detectionPoint
  · have x := TierSelectors631.family2X_value rho arithmetic
    have y := TierSelectors631.family2Y_value rho arithmetic
    simp only [CompilerArithmeticTransport41.copy,eval,Int.cast_one,one_mul,add_zero,Int.cast_sub,Int.cast_neg,Int.cast_ofNat,neg_mul,one,mul_one] at x y
    have selectedX := coordinate_choice (rho 121566) (rho 33790) (rho 154386)
      (49822839976625491399435002605169580882773999909559575334089637637825427273330:F) (17832230285398775523840151435063191920633280288053987250961356462684628833490:F) (flagged w) (rho 108486) flag (by
        rw [x]
        ring)
    have selectedY := coordinate_choice (rho 121568) (rho 33792) (rho 154388)
      (29108985603249989484651727880329493522712908252517904247459350893053326313050:F) (52236742954115892447572473178524297982305297140137344394933767595493156073169:F) (flagged w) (rho 108486) flag (by
        rw [y]
        ring)
    rw [px,dx] at selectedX
    rw [py,dy] at selectedY
    cases chosen : flagged w <;>
      simp only [chosen,Bool.false_eq_true,if_false,if_true] at selectedX selectedY
    all_goals
      change Group.Point.mk _ _=SubgroupSeedCompletion203.fieldPoint
        (if (decide ((2:Nat)=1) || flagged w) then DetectionGroupDomain611.selected c w
          else PayloadGroupDomain557.selected (DetectionGroupDomain611.baseCrypto c) w)
      simp only [chosen,show decide ((2:Nat)=1)=false by decide,Bool.false_or,
        Bool.false_eq_true,if_false,if_true,SubgroupSeedCompletion203.fieldPoint]
      apply congrArg₂ Group.Point.mk
      · change eval rho [(121566,1),(154386,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)] = _
        have evaluated : eval rho [(121566,1),(154386,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)]=rho 121566+(rho 154386+(49822839976625491399435002605169580882773999909559575334089637637825427273330:F)) := by
          simp only [eval,Int.cast_one,one_mul,add_zero,Int.cast_ofNat,one,mul_one]
        exact evaluated.trans selectedX
      · change eval rho [(121568,1),(154388,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)] = _
        have evaluated : eval rho [(121568,1),(154388,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)]=rho 121568+(rho 154388+(29108985603249989484651727880329493522712908252517904247459350893053326313050:F)) := by
          simp only [eval,Int.cast_one,one_mul,add_zero,Int.cast_ofNat,one,mul_one]
        exact evaluated.trans selectedY
  · have x := TierSelectors631.family3X_value rho arithmetic
    have y := TierSelectors631.family3Y_value rho arithmetic
    simp only [CompilerArithmeticTransport41.copy,eval,Int.cast_one,one_mul,add_zero,Int.cast_sub,Int.cast_neg,Int.cast_ofNat,neg_mul,one,mul_one] at x y
    have selectedX := coordinate_choice (rho 121566) (rho 33790) (rho 161679)
      (49822839976625491399435002605169580882773999909559575334089637637825427273330:F) (17832230285398775523840151435063191920633280288053987250961356462684628833490:F) (flagged w) (rho 108486) flag (by
        rw [x]
        ring)
    have selectedY := coordinate_choice (rho 121568) (rho 33792) (rho 161681)
      (29108985603249989484651727880329493522712908252517904247459350893053326313050:F) (52236742954115892447572473178524297982305297140137344394933767595493156073169:F) (flagged w) (rho 108486) flag (by
        rw [y]
        ring)
    rw [px,dx] at selectedX
    rw [py,dy] at selectedY
    cases chosen : flagged w <;>
      simp only [chosen,Bool.false_eq_true,if_false,if_true] at selectedX selectedY
    all_goals
      change Group.Point.mk _ _=SubgroupSeedCompletion203.fieldPoint
        (if (decide ((3:Nat)=1) || flagged w) then DetectionGroupDomain611.selected c w
          else PayloadGroupDomain557.selected (DetectionGroupDomain611.baseCrypto c) w)
      simp only [chosen,show decide ((3:Nat)=1)=false by decide,Bool.false_or,
        Bool.false_eq_true,if_false,if_true,SubgroupSeedCompletion203.fieldPoint]
      apply congrArg₂ Group.Point.mk
      · change eval rho [(121566,1),(161679,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)] = _
        have evaluated : eval rho [(121566,1),(161679,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)]=rho 121566+(rho 161679+(49822839976625491399435002605169580882773999909559575334089637637825427273330:F)) := by
          simp only [eval,Int.cast_one,one_mul,add_zero,Int.cast_ofNat,one,mul_one]
        exact evaluated.trans selectedX
      · change eval rho [(121568,1),(161681,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)] = _
        have evaluated : eval rho [(121568,1),(161681,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)]=rho 121568+(rho 161681+(29108985603249989484651727880329493522712908252517904247459350893053326313050:F)) := by
          simp only [eval,Int.cast_one,one_mul,add_zero,Int.cast_ofNat,one,mul_one]
        exact evaluated.trans selectedY
  · have x := TierSelectors631.family4X_value rho arithmetic
    have y := TierSelectors631.family4Y_value rho arithmetic
    simp only [CompilerArithmeticTransport41.copy,eval,Int.cast_one,one_mul,add_zero,Int.cast_sub,Int.cast_neg,Int.cast_ofNat,neg_mul,one,mul_one] at x y
    have selectedX := coordinate_choice (rho 121566) (rho 33790) (rho 168972)
      (49822839976625491399435002605169580882773999909559575334089637637825427273330:F) (17832230285398775523840151435063191920633280288053987250961356462684628833490:F) (flagged w) (rho 108486) flag (by
        rw [x]
        ring)
    have selectedY := coordinate_choice (rho 121568) (rho 33792) (rho 168974)
      (29108985603249989484651727880329493522712908252517904247459350893053326313050:F) (52236742954115892447572473178524297982305297140137344394933767595493156073169:F) (flagged w) (rho 108486) flag (by
        rw [y]
        ring)
    rw [px,dx] at selectedX
    rw [py,dy] at selectedY
    cases chosen : flagged w <;>
      simp only [chosen,Bool.false_eq_true,if_false,if_true] at selectedX selectedY
    all_goals
      change Group.Point.mk _ _=SubgroupSeedCompletion203.fieldPoint
        (if (decide ((4:Nat)=1) || flagged w) then DetectionGroupDomain611.selected c w
          else PayloadGroupDomain557.selected (DetectionGroupDomain611.baseCrypto c) w)
      simp only [chosen,show decide ((4:Nat)=1)=false by decide,Bool.false_or,
        Bool.false_eq_true,if_false,if_true,SubgroupSeedCompletion203.fieldPoint]
      apply congrArg₂ Group.Point.mk
      · change eval rho [(121566,1),(168972,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)] = _
        have evaluated : eval rho [(121566,1),(168972,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)]=rho 121566+(rho 168972+(49822839976625491399435002605169580882773999909559575334089637637825427273330:F)) := by
          simp only [eval,Int.cast_one,one_mul,add_zero,Int.cast_ofNat,one,mul_one]
        exact evaluated.trans selectedX
      · change eval rho [(121568,1),(168974,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)] = _
        have evaluated : eval rho [(121568,1),(168974,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)]=rho 121568+(rho 168974+(29108985603249989484651727880329493522712908252517904247459350893053326313050:F)) := by
          simp only [eval,Int.cast_one,one_mul,add_zero,Int.cast_ofNat,one,mul_one]
        exact evaluated.trans selectedY

theorem payload_inputs (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    PayloadInputFrame566.Inputs (TierFlagBindings630.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) w := by
  unfold TierFlagBindings630.assignment TierBindings617.assignment OwnershipBindings604.assignment
    PublishedInverseSeed592.assignment PublishedPointSeed584.assignment PayloadBindings565.assignment FixedFamilyBindings551.assignment
  exact PayloadInputFrame566.rk _ (DetectionGroupDomain611.baseCrypto c) w legal
    rkInitial authInitial initial senderInitial receiverInitial

theorem coordinates (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (family : Fin 5) :
    VariableWindowJoin443.point (TierFlagBindings630.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) (baseX family) (baseY family)=
      model.coordinates (TierGroupDomain612.represented c w family legal) := by
  rw [selected _ c w family (TierFlagBindings630.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (TierFlagBindings630.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial) (payload_inputs original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (DetectionBase627.inputs (TierFlagSeed623.seed original w) c w legal
      rkInitial authInitial initial senderInitial receiverInitial)
    (TierFlagBindings630.flagged_value original c w legal rkInitial authInitial initial senderInitial receiverInitial)]
  exact (TierGroupDomain612.coordinates c w family legal).symm

end ShielddSecurity.TierBase632

set_option pp.all true in
#check @ShielddSecurity.TierBase632.payload_selected
#print axioms ShielddSecurity.TierBase632.payload_selected

set_option pp.all true in
#check @ShielddSecurity.TierBase632.coordinate_choice
#print axioms ShielddSecurity.TierBase632.coordinate_choice

set_option pp.all true in
#check @ShielddSecurity.TierBase632.selected
#print axioms ShielddSecurity.TierBase632.selected

set_option pp.all true in
#check @ShielddSecurity.TierBase632.payload_inputs
#print axioms ShielddSecurity.TierBase632.payload_inputs

set_option pp.all true in
#check @ShielddSecurity.TierBase632.coordinates
#print axioms ShielddSecurity.TierBase632.coordinates
