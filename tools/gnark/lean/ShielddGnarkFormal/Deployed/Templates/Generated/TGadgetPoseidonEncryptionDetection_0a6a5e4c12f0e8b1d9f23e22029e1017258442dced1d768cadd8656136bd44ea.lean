import ShielddGnarkFormal.Deployed.Templates.Relations.TGadgetPoseidonEncryptionDetection_0a6a5e4c12f0e8b1d9f23e22029e1017258442dced1d768cadd8656136bd44ea
import ShielddGnarkFormal.Deployed.Templates.Semantics.TGadgetPoseidonEncryptionDetection_0a6a5e4c12f0e8b1d9f23e22029e1017258442dced1d768cadd8656136bd44ea

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

namespace Shieldd.GnarkFormal.Deployed.Templates.Generated.TGadgetPoseidonEncryptionDetection_0a6a5e4c12f0e8b1d9f23e22029e1017258442dced1d768cadd8656136bd44ea

abbrev F := Shieldd.GnarkFormal.Deployed.Templates.Semantics.TGadgetPoseidonEncryptionDetection_0a6a5e4c12f0e8b1d9f23e22029e1017258442dced1d768cadd8656136bd44ea.F

def relation (rho : Nat -> F) : Prop := Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetPoseidonEncryptionDetection_0a6a5e4c12f0e8b1d9f23e22029e1017258442dced1d768cadd8656136bd44ea.relation rho

def spec (rho : Nat -> F) : Prop := Shieldd.GnarkFormal.Deployed.Templates.Semantics.TGadgetPoseidonEncryptionDetection_0a6a5e4c12f0e8b1d9f23e22029e1017258442dced1d768cadd8656136bd44ea.spec rho

theorem sound (rho : Nat → F) (h : relation rho) : spec rho := by
             exact Shieldd.GnarkFormal.Deployed.Templates.Semantics.TGadgetPoseidonEncryptionDetection_0a6a5e4c12f0e8b1d9f23e22029e1017258442dced1d768cadd8656136bd44ea.sound rho h
end Shieldd.GnarkFormal.Deployed.Templates.Generated.TGadgetPoseidonEncryptionDetection_0a6a5e4c12f0e8b1d9f23e22029e1017258442dced1d768cadd8656136bd44ea
