import ShielddGnarkFormal.ChoiceFreeZModCast
import ShielddGnarkFormal.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0Poseidon.FullTail

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Shieldd.GnarkFormal.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0Poseidon

open scoped Shieldd.GnarkFormal.ChoiceFreeZMod

open Shieldd.GnarkFormal.Poseidon3Bridge
open Shieldd.GnarkFormal.Deployed.Poseidon3Link

variable [Fact (Nat.Prime Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.Order)]

instance : Fact (Nat.Prime Shieldd.GnarkFormal.Extracted.PoseidonHash3.Order) :=
  inferInstanceAs (Fact (Nat.Prime Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.Order))

theorem spec38_eq_permSpec (sin0 : F) (sin1 : F) (sin2 : F) :
    (spec38 sin0 sin1 sin2)[1] = permSpec3 domainLit sin0 sin1 sin2 := by
  unfold permSpec3 domainLit
  rfl

end Shieldd.GnarkFormal.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0Poseidon
