import ShielddGnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec
import ShielddGnarkFormal.Deployed.Templates.Semantics.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

namespace Shieldd.GnarkFormal.Deployed.Templates.Generated.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec

abbrev F := Shieldd.GnarkFormal.Deployed.Templates.Semantics.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.F

def relation (rho : Nat -> F) : Prop := Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relation rho

def spec (rho : Nat -> F) : Prop := Shieldd.GnarkFormal.Deployed.Templates.Semantics.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.spec rho

theorem sound (rho : Nat → F) (h : relation rho) : spec rho := by
             exact Shieldd.GnarkFormal.Deployed.Templates.Semantics.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.sound rho h
end Shieldd.GnarkFormal.Deployed.Templates.Generated.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec
