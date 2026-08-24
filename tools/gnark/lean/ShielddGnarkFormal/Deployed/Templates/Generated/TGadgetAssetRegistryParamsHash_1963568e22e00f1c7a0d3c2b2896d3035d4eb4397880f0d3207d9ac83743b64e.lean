import ShielddGnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e
import ShielddGnarkFormal.Deployed.Templates.Semantics.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

namespace Shieldd.GnarkFormal.Deployed.Templates.Generated.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e

abbrev F := Shieldd.GnarkFormal.Deployed.Templates.Semantics.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.F

def relation (rho : Nat -> F) : Prop := Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relation rho

def spec (rho : Nat -> F) : Prop := Shieldd.GnarkFormal.Deployed.Templates.Semantics.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.spec rho

theorem sound (rho : Nat → F) (h : relation rho) : spec rho := by
             exact Shieldd.GnarkFormal.Deployed.Templates.Semantics.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.sound rho h
end Shieldd.GnarkFormal.Deployed.Templates.Generated.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e
