import ShielddGnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db
import ShielddGnarkFormal.Deployed.Templates.Semantics.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

namespace Shieldd.GnarkFormal.Deployed.Templates.Generated.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db

abbrev F := Shieldd.GnarkFormal.Deployed.Templates.Semantics.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.F

def relation (rho : Nat -> F) : Prop := Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relation rho

def spec (rho : Nat -> F) : Prop := Shieldd.GnarkFormal.Deployed.Templates.Semantics.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.spec rho

theorem sound (rho : Nat → F) (h : relation rho) : spec rho := by
             exact Shieldd.GnarkFormal.Deployed.Templates.Semantics.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.sound rho h
end Shieldd.GnarkFormal.Deployed.Templates.Generated.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db
