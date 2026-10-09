import ShielddSecurity.Scalar
import ShielddSecurity.RuntimeRnkHash2_Data
set_option maxHeartbeats 250000
set_option maxRecDepth 2048
namespace ShielddSecurity.NativeAssetHashParameters
variable {F : Type} [Field F] [CharP F Scalar.modulus]
def smallParameters : Poseidon.Parameters F 3 :=
  Poseidon.castParameters RuntimeHashBlock_authorization_rnk_permutation2_0.parameters

end ShielddSecurity.NativeAssetHashParameters
