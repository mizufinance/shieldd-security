import ShielddSecurity.UserPointDomain351
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationDhNonzero475
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294

theorem x_nonzero (point : Group.Point F)
    (member : CapturedSubgroupModel199.Member model point)
    (nonidentity : point≠Group.identityPoint) : point.x≠0 :=
  SubgroupNonidentity350.member_x_nonzero model point member nonidentity
end ShielddSecurity.AuthorizationDhNonzero475
set_option pp.all true in
#check @ShielddSecurity.AuthorizationDhNonzero475.x_nonzero
#print axioms ShielddSecurity.AuthorizationDhNonzero475.x_nonzero
