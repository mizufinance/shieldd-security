import ShielddSecurity.UserLifecycleConstruction349
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SubgroupNonidentity350
variable {F J : Type} [Field F] [AddCommGroup J]

theorem scalar_order_odd : TransferCore.scalarOrder%2=1 := by decide +kernel

theorem zero_x_double_identity {d : F} (model : Group.StandardCurveModel J d)
    (point : J) (zeroX : (model.coordinates point).x=0) : point+point=0 := by
  have yy : (model.coordinates point).y*(model.coordinates point).y=1 := by
    simpa only [Group.OnCurve,zeroX,mul_zero,zero_mul,sub_zero,add_zero] using model.onCurve point
  apply model.injective
  rw [model.addition,model.identity]
  simp only [Group.affineAdd,Group.cross,Group.diagonal,Group.delta,zeroX,mul_zero,zero_mul,
    add_zero,zero_add,sub_zero,div_one,yy,Group.identityPoint]

theorem killed_by_two_and_scalar (point : J) (two : point+point=0)
    (scalar : TransferCore.scalarOrder • point=0) : point=0 := by
  have double : (2:Nat) • point=0 := by simpa only [two_nsmul] using two
  have decomposition : (TransferCore.scalarOrder/2)*2+1=TransferCore.scalarOrder := by
    have identity := Nat.mod_add_div TransferCore.scalarOrder 2
    rw [scalar_order_odd] at identity
    omega
  rw [← decomposition,add_nsmul,Nat.mul_comm (TransferCore.scalarOrder/2) 2,mul_nsmul,double,nsmul_zero,one_nsmul,zero_add] at scalar
  exact scalar

theorem member_x_nonzero {d : F} (model : Group.StandardCurveModel J d)
    (point : Group.Point F) (member : CapturedSubgroupModel199.Member model point)
    (nonidentity : point≠Group.identityPoint) : point.x≠0 := by
  rcases member with ⟨represented,coordinates,killed⟩
  intro zeroX
  have zeroCoordinate : (model.coordinates represented).x=0 := by rw [coordinates]; exact zeroX
  have zero := killed_by_two_and_scalar represented (zero_x_double_identity model represented zeroCoordinate) killed
  apply nonidentity
  exact coordinates.symm.trans (by rw [zero,model.identity])
end ShielddSecurity.SubgroupNonidentity350

set_option pp.all true in
#check @ShielddSecurity.SubgroupNonidentity350.scalar_order_odd
#print axioms ShielddSecurity.SubgroupNonidentity350.scalar_order_odd

set_option pp.all true in
#check @ShielddSecurity.SubgroupNonidentity350.zero_x_double_identity
#print axioms ShielddSecurity.SubgroupNonidentity350.zero_x_double_identity

set_option pp.all true in
#check @ShielddSecurity.SubgroupNonidentity350.killed_by_two_and_scalar
#print axioms ShielddSecurity.SubgroupNonidentity350.killed_by_two_and_scalar

set_option pp.all true in
#check @ShielddSecurity.SubgroupNonidentity350.member_x_nonzero
#print axioms ShielddSecurity.SubgroupNonidentity350.member_x_nonzero
