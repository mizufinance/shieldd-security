import ShielddGnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec
import ShielddGnarkFormal.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34Poseidon.SemanticBridge
import ShielddGnarkFormal.Deployed.PrimeOrder
import Mathlib.Tactic.LinearCombination

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

namespace Shieldd.GnarkFormal.Deployed.Templates.Semantics.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec

def Order : Nat := 8444461749428370424248824938781546531375899335154063827935233455917409239041
abbrev F := ZMod Order

instance templateFactPrime : Fact (Nat.Prime Order) :=
  ⟨Shieldd.GnarkFormal.Deployed.decaf377ScalarFieldPrime⟩

local instance (priority := 2000) providerCommRing : CommRing F := ZMod.commRing _
local instance (priority := 3000) providerAdd : Add F := (ZMod.commRing _).toAdd
local instance (priority := 3000) providerAddSemigroup : AddSemigroup F := (ZMod.commRing _).toAddSemigroup
local instance (priority := 3000) providerMul : Mul F := (ZMod.commRing _).toMul
local instance (priority := 3000) providerNatCast : NatCast F := (ZMod.commRing _).toNatCast
local instance (priority := 3000) providerZero : Zero F := (ZMod.commRing _).toZero
local instance (priority := 3000) providerOne : One F := (ZMod.commRing _).toOne
local instance (priority := 3000) providerNeg : Neg F := (ZMod.commRing _).toNeg
local instance (priority := 3000) providerSub : Sub F := (ZMod.commRing _).toSub
local instance (priority := 3000) providerMulOneClass : MulOneClass F := (ZMod.commRing _).toMulOneClass
local instance (priority := 3000) providerCommSemiring : CommSemiring F := (ZMod.commRing _).toCommSemiring
local instance (priority := 3000) providerRing : Ring F := (ZMod.commRing _).toRing

def output (rho : Nat → F) : F :=
  Shieldd.GnarkFormal.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34Poseidon.s38_1 (rho 372) (rho 377) (rho 382) (rho 387) (rho 392) (rho 397)

def spec (rho : Nat → F) : Prop :=
  output rho =
    Shieldd.GnarkFormal.Poseidon5Bridge.permSpec5
      (4269006203104973867634438910267250913271743773478037782164242111046258415985 : F)
      ((-1 : F) * rho 1 + rho 2) ((-1 : F) * rho 8 + rho 9) (rho 15) (rho 21) (rho 27)

theorem template_part0_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart0 rho)
    {k : F → F → F → F → F → F → Prop} (hk : k (rho 8) (rho 9) (rho 15) (rho 21) (rho 27) (rho 7)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg0 (rho 1) (rho 2) (rho 8) (rho 9) (rho 15) (rho 21) (rho 27) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart0 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow0 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow1 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow2 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow3 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow4 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg0
  refine ⟨(rho 3), (rho 4), (rho 5), (rho 6), (rho 7), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part1_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart1 rho)
    {k : F → F → F → F → F → Prop} (hk : k (rho 7) (rho 15) (rho 21) (rho 27) (rho 14)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg1 (rho 7) (rho 8) (rho 9) (rho 15) (rho 21) (rho 27) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart1 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow5 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow6 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow7 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow8 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow9 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg1
  refine ⟨(rho 10), (rho 11), (rho 12), (rho 13), (rho 14), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part2_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart2 rho)
    {k : F → F → F → F → F → Prop} (hk : k (rho 7) (rho 14) (rho 21) (rho 27) (rho 20)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg2 (rho 7) (rho 14) (rho 15) (rho 21) (rho 27) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart2 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow10 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow11 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow12 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow13 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow14 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg2
  refine ⟨(rho 16), (rho 17), (rho 18), (rho 19), (rho 20), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part3_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart3 rho)
    {k : F → F → F → F → F → Prop} (hk : k (rho 7) (rho 14) (rho 20) (rho 27) (rho 26)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg3 (rho 7) (rho 14) (rho 20) (rho 21) (rho 27) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart3 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow15 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow16 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow17 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow18 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow19 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg3
  refine ⟨(rho 22), (rho 23), (rho 24), (rho 25), (rho 26), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part4_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart4 rho)
    {k : F → F → F → F → F → Prop} (hk : k (rho 7) (rho 14) (rho 20) (rho 26) (rho 32)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg4 (rho 7) (rho 14) (rho 20) (rho 26) (rho 27) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart4 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow20 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow21 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow22 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow23 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow24 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg4
  refine ⟨(rho 28), (rho 29), (rho 30), (rho 31), (rho 32), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part5_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart5 rho)
    {k : F → F → F → F → F → F → Prop} (hk : k (rho 7) (rho 14) (rho 20) (rho 26) (rho 32) (rho 37)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg5 (rho 7) (rho 14) (rho 20) (rho 26) (rho 32) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart5 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow25 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow26 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow27 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow28 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow29 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg5
  refine ⟨(rho 33), (rho 34), (rho 35), (rho 36), (rho 37), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part6_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart6 rho)
    {k : F → F → F → F → F → F → F → Prop} (hk : k (rho 7) (rho 14) (rho 20) (rho 26) (rho 32) (rho 37) (rho 42)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg6 (rho 7) (rho 14) (rho 20) (rho 26) (rho 32) (rho 37) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart6 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow30 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow31 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow32 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow33 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow34 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg6
  refine ⟨(rho 38), (rho 39), (rho 40), (rho 41), (rho 42), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part7_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart7 rho)
    {k : F → F → F → F → F → F → F → F → Prop} (hk : k (rho 7) (rho 14) (rho 20) (rho 26) (rho 32) (rho 37) (rho 42) (rho 47)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg7 (rho 7) (rho 14) (rho 20) (rho 26) (rho 32) (rho 37) (rho 42) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart7 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow35 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow36 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow37 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow38 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow39 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg7
  refine ⟨(rho 43), (rho 44), (rho 45), (rho 46), (rho 47), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part8_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart8 rho)
    {k : F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 7) (rho 14) (rho 20) (rho 26) (rho 32) (rho 37) (rho 42) (rho 47) (rho 52)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg8 (rho 7) (rho 14) (rho 20) (rho 26) (rho 32) (rho 37) (rho 42) (rho 47) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart8 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow40 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow41 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow42 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow43 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow44 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg8
  refine ⟨(rho 48), (rho 49), (rho 50), (rho 51), (rho 52), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part9_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart9 rho)
    {k : F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 7) (rho 14) (rho 20) (rho 26) (rho 32) (rho 37) (rho 42) (rho 47) (rho 52) (rho 57)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg9 (rho 7) (rho 14) (rho 20) (rho 26) (rho 32) (rho 37) (rho 42) (rho 47) (rho 52) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart9 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow45 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow46 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow47 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow48 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow49 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg9
  refine ⟨(rho 53), (rho 54), (rho 55), (rho 56), (rho 57), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part10_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart10 rho)
    {k : F → F → F → F → F → F → Prop} (hk : k (rho 37) (rho 42) (rho 47) (rho 52) (rho 57) (rho 62)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg10 (rho 7) (rho 14) (rho 20) (rho 26) (rho 32) (rho 37) (rho 42) (rho 47) (rho 52) (rho 57) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart10 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow50 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow51 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow52 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow53 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow54 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg10
  refine ⟨(rho 58), (rho 59), (rho 60), (rho 61), (rho 62), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part11_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart11 rho)
    {k : F → F → F → F → F → F → F → Prop} (hk : k (rho 37) (rho 42) (rho 47) (rho 52) (rho 57) (rho 62) (rho 67)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg11 (rho 37) (rho 42) (rho 47) (rho 52) (rho 57) (rho 62) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart11 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow55 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow56 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow57 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow58 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow59 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg11
  refine ⟨(rho 63), (rho 64), (rho 65), (rho 66), (rho 67), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part12_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart12 rho)
    {k : F → F → F → F → F → F → F → F → Prop} (hk : k (rho 37) (rho 42) (rho 47) (rho 52) (rho 57) (rho 62) (rho 67) (rho 72)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg12 (rho 37) (rho 42) (rho 47) (rho 52) (rho 57) (rho 62) (rho 67) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart12 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow60 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow61 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow62 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow63 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow64 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg12
  refine ⟨(rho 68), (rho 69), (rho 70), (rho 71), (rho 72), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part13_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart13 rho)
    {k : F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 37) (rho 42) (rho 47) (rho 52) (rho 57) (rho 62) (rho 67) (rho 72) (rho 77)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg13 (rho 37) (rho 42) (rho 47) (rho 52) (rho 57) (rho 62) (rho 67) (rho 72) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart13 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow65 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow66 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow67 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow68 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow69 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg13
  refine ⟨(rho 73), (rho 74), (rho 75), (rho 76), (rho 77), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part14_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart14 rho)
    {k : F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 37) (rho 42) (rho 47) (rho 52) (rho 57) (rho 62) (rho 67) (rho 72) (rho 77) (rho 82)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg14 (rho 37) (rho 42) (rho 47) (rho 52) (rho 57) (rho 62) (rho 67) (rho 72) (rho 77) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart14 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow70 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow71 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow72 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow73 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow74 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg14
  refine ⟨(rho 78), (rho 79), (rho 80), (rho 81), (rho 82), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part15_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart15 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 37) (rho 42) (rho 47) (rho 52) (rho 57) (rho 62) (rho 67) (rho 72) (rho 77) (rho 82) (rho 87)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg15 (rho 37) (rho 42) (rho 47) (rho 52) (rho 57) (rho 62) (rho 67) (rho 72) (rho 77) (rho 82) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart15 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow75 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow76 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow77 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow78 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow79 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg15
  refine ⟨(rho 83), (rho 84), (rho 85), (rho 86), (rho 87), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part16_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart16 rho)
    {k : F → F → F → F → F → F → Prop} (hk : k (rho 67) (rho 72) (rho 77) (rho 82) (rho 87) (rho 92)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg16 (rho 37) (rho 42) (rho 47) (rho 52) (rho 57) (rho 62) (rho 67) (rho 72) (rho 77) (rho 82) (rho 87) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart16 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow80 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow81 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow82 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow83 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow84 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg16
  refine ⟨(rho 88), (rho 89), (rho 90), (rho 91), (rho 92), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part17_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart17 rho)
    {k : F → F → F → F → F → F → F → Prop} (hk : k (rho 67) (rho 72) (rho 77) (rho 82) (rho 87) (rho 92) (rho 97)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg17 (rho 67) (rho 72) (rho 77) (rho 82) (rho 87) (rho 92) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart17 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow85 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow86 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow87 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow88 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow89 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg17
  refine ⟨(rho 93), (rho 94), (rho 95), (rho 96), (rho 97), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part18_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart18 rho)
    {k : F → F → F → F → F → F → F → F → Prop} (hk : k (rho 67) (rho 72) (rho 77) (rho 82) (rho 87) (rho 92) (rho 97) (rho 102)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg18 (rho 67) (rho 72) (rho 77) (rho 82) (rho 87) (rho 92) (rho 97) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart18 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow90 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow91 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow92 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow93 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow94 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg18
  refine ⟨(rho 98), (rho 99), (rho 100), (rho 101), (rho 102), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part19_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart19 rho)
    {k : F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 67) (rho 72) (rho 77) (rho 82) (rho 87) (rho 92) (rho 97) (rho 102) (rho 107)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg19 (rho 67) (rho 72) (rho 77) (rho 82) (rho 87) (rho 92) (rho 97) (rho 102) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart19 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow95 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow96 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow97 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow98 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow99 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg19
  refine ⟨(rho 103), (rho 104), (rho 105), (rho 106), (rho 107), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part20_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart20 rho)
    {k : F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 67) (rho 72) (rho 77) (rho 82) (rho 87) (rho 92) (rho 97) (rho 102) (rho 107) (rho 112)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg20 (rho 67) (rho 72) (rho 77) (rho 82) (rho 87) (rho 92) (rho 97) (rho 102) (rho 107) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart20 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow100 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow101 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow102 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow103 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow104 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg20
  refine ⟨(rho 108), (rho 109), (rho 110), (rho 111), (rho 112), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part21_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart21 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 67) (rho 72) (rho 77) (rho 82) (rho 87) (rho 92) (rho 97) (rho 102) (rho 107) (rho 112) (rho 117)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg21 (rho 67) (rho 72) (rho 77) (rho 82) (rho 87) (rho 92) (rho 97) (rho 102) (rho 107) (rho 112) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart21 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow105 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow106 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow107 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow108 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow109 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg21
  refine ⟨(rho 113), (rho 114), (rho 115), (rho 116), (rho 117), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part22_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart22 rho)
    {k : F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg22 (rho 67) (rho 72) (rho 77) (rho 82) (rho 87) (rho 92) (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart22 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow110 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow111 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow112 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow113 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow114 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg22
  refine ⟨(rho 118), (rho 119), (rho 120), (rho 121), (rho 122), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part23_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart23 rho)
    {k : F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg23 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart23 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow115 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow116 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow117 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow118 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow119 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg23
  refine ⟨(rho 123), (rho 124), (rho 125), (rho 126), (rho 127), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part24_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart24 rho)
    {k : F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg24 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart24 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow120 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow121 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow122 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow123 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow124 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg24
  refine ⟨(rho 128), (rho 129), (rho 130), (rho 131), (rho 132), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part25_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart25 rho)
    {k : F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg25 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart25 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow125 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow126 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow127 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow128 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow129 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg25
  refine ⟨(rho 133), (rho 134), (rho 135), (rho 136), (rho 137), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part26_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart26 rho)
    {k : F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg26 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart26 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow130 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow131 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow132 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow133 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow134 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg26
  refine ⟨(rho 138), (rho 139), (rho 140), (rho 141), (rho 142), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part27_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart27 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg27 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart27 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow135 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow136 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow137 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow138 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow139 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg27
  refine ⟨(rho 143), (rho 144), (rho 145), (rho 146), (rho 147), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part28_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart28 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg28 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart28 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow140 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow141 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow142 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow143 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow144 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg28
  refine ⟨(rho 148), (rho 149), (rho 150), (rho 151), (rho 152), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part29_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart29 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg29 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart29 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow145 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow146 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow147 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow148 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow149 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg29
  refine ⟨(rho 153), (rho 154), (rho 155), (rho 156), (rho 157), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part30_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart30 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg30 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart30 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow150 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow151 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow152 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow153 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow154 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg30
  refine ⟨(rho 158), (rho 159), (rho 160), (rho 161), (rho 162), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part31_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart31 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg31 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart31 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow155 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow156 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow157 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow158 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow159 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg31
  refine ⟨(rho 163), (rho 164), (rho 165), (rho 166), (rho 167), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part32_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart32 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg32 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart32 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow160 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow161 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow162 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow163 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow164 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg32
  refine ⟨(rho 168), (rho 169), (rho 170), (rho 171), (rho 172), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part33_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart33 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg33 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart33 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow165 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow166 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow167 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow168 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow169 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg33
  refine ⟨(rho 173), (rho 174), (rho 175), (rho 176), (rho 177), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part34_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart34 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg34 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart34 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow170 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow171 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow172 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow173 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow174 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg34
  refine ⟨(rho 178), (rho 179), (rho 180), (rho 181), (rho 182), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part35_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart35 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg35 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart35 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow175 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow176 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow177 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow178 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow179 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg35
  refine ⟨(rho 183), (rho 184), (rho 185), (rho 186), (rho 187), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part36_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart36 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg36 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart36 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow180 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow181 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow182 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow183 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow184 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg36
  refine ⟨(rho 188), (rho 189), (rho 190), (rho 191), (rho 192), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part37_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart37 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg37 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart37 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow185 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow186 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow187 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow188 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow189 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg37
  refine ⟨(rho 193), (rho 194), (rho 195), (rho 196), (rho 197), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part38_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart38 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg38 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart38 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow190 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow191 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow192 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow193 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow194 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg38
  refine ⟨(rho 198), (rho 199), (rho 200), (rho 201), (rho 202), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part39_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart39 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg39 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart39 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow195 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow196 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow197 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow198 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow199 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg39
  refine ⟨(rho 203), (rho 204), (rho 205), (rho 206), (rho 207), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part40_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart40 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg40 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart40 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow200 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow201 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow202 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow203 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow204 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg40
  refine ⟨(rho 208), (rho 209), (rho 210), (rho 211), (rho 212), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part41_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart41 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg41 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart41 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow205 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow206 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow207 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow208 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow209 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg41
  refine ⟨(rho 213), (rho 214), (rho 215), (rho 216), (rho 217), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part42_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart42 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg42 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart42 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow210 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow211 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow212 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow213 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow214 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg42
  refine ⟨(rho 218), (rho 219), (rho 220), (rho 221), (rho 222), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part43_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart43 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg43 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart43 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow215 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow216 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow217 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow218 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow219 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg43
  refine ⟨(rho 223), (rho 224), (rho 225), (rho 226), (rho 227), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part44_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart44 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg44 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart44 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow220 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow221 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow222 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow223 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow224 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg44
  refine ⟨(rho 228), (rho 229), (rho 230), (rho 231), (rho 232), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part45_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart45 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) (rho 237)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg45 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart45 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow225 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow226 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow227 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow228 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow229 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg45
  refine ⟨(rho 233), (rho 234), (rho 235), (rho 236), (rho 237), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part46_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart46 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) (rho 237) (rho 242)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg46 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) (rho 237) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart46 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow230 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow231 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow232 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow233 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow234 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg46
  refine ⟨(rho 238), (rho 239), (rho 240), (rho 241), (rho 242), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part47_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart47 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) (rho 237) (rho 242) (rho 247)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg47 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) (rho 237) (rho 242) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart47 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow235 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow236 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow237 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow238 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow239 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg47
  refine ⟨(rho 243), (rho 244), (rho 245), (rho 246), (rho 247), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part48_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart48 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) (rho 237) (rho 242) (rho 247) (rho 252)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg48 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) (rho 237) (rho 242) (rho 247) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart48 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow240 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow241 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow242 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow243 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow244 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg48
  refine ⟨(rho 248), (rho 249), (rho 250), (rho 251), (rho 252), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part49_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart49 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) (rho 237) (rho 242) (rho 247) (rho 252) (rho 257)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg49 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) (rho 237) (rho 242) (rho 247) (rho 252) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart49 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow245 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow246 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow247 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow248 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow249 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg49
  refine ⟨(rho 253), (rho 254), (rho 255), (rho 256), (rho 257), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc0Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc0Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc0Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc0Part1, choiceFreeAddAssoc] using h4

theorem template_part50_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart50 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) (rho 237) (rho 242) (rho 247) (rho 252) (rho 257) (rho 262)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg50 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) (rho 237) (rho 242) (rho 247) (rho 252) (rho 257) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart50 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow250 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow251 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow252 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow253 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow254 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg50
  refine ⟨(rho 258), (rho 259), (rho 260), (rho 261), (rho 262), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc1, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc1Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc1Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc1, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc1Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc1Part1, choiceFreeAddAssoc] using h4

theorem template_part51_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart51 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) (rho 237) (rho 242) (rho 247) (rho 252) (rho 257) (rho 262) (rho 267)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg51 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) (rho 237) (rho 242) (rho 247) (rho 252) (rho 257) (rho 262) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart51 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow255 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow256 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow257 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow258 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow259 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg51
  refine ⟨(rho 263), (rho 264), (rho 265), (rho 266), (rho 267), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc2, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc2Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc2Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc2, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc2Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc2Part1, choiceFreeAddAssoc] using h4

theorem template_part52_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart52 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) (rho 237) (rho 242) (rho 247) (rho 252) (rho 257) (rho 262) (rho 267) (rho 272)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg52 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) (rho 237) (rho 242) (rho 247) (rho 252) (rho 257) (rho 262) (rho 267) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart52 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow260 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow261 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow262 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow263 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow264 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg52
  refine ⟨(rho 268), (rho 269), (rho 270), (rho 271), (rho 272), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc3, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc3Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc3Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc3, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc3Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc3Part1, choiceFreeAddAssoc] using h4

theorem template_part53_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart53 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) (rho 237) (rho 242) (rho 247) (rho 252) (rho 257) (rho 262) (rho 267) (rho 272) (rho 277)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg53 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) (rho 237) (rho 242) (rho 247) (rho 252) (rho 257) (rho 262) (rho 267) (rho 272) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart53 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow265 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow266 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow267 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow268 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow269 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg53
  refine ⟨(rho 273), (rho 274), (rho 275), (rho 276), (rho 277), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc4, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc4Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc4Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc4, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc4Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc4Part1, choiceFreeAddAssoc] using h4

theorem template_part54_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart54 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) (rho 237) (rho 242) (rho 247) (rho 252) (rho 257) (rho 262) (rho 267) (rho 272) (rho 277) (rho 282)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg54 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) (rho 237) (rho 242) (rho 247) (rho 252) (rho 257) (rho 262) (rho 267) (rho 272) (rho 277) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart54 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow270 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow271 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow272 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow273 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow274 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg54
  refine ⟨(rho 278), (rho 279), (rho 280), (rho 281), (rho 282), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc5, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc5Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc5Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc5, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc5Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc5Part1, choiceFreeAddAssoc] using h4

theorem template_part55_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart55 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) (rho 237) (rho 242) (rho 247) (rho 252) (rho 257) (rho 262) (rho 267) (rho 272) (rho 277) (rho 282) (rho 287)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg55 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) (rho 237) (rho 242) (rho 247) (rho 252) (rho 257) (rho 262) (rho 267) (rho 272) (rho 277) (rho 282) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart55 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow275 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow276 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow277 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow278 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow279 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg55
  refine ⟨(rho 283), (rho 284), (rho 285), (rho 286), (rho 287), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc6, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc6Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc6Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc6, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc6Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc6Part1, choiceFreeAddAssoc] using h4

theorem template_part56_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart56 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) (rho 237) (rho 242) (rho 247) (rho 252) (rho 257) (rho 262) (rho 267) (rho 272) (rho 277) (rho 282) (rho 287) (rho 292)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg56 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) (rho 237) (rho 242) (rho 247) (rho 252) (rho 257) (rho 262) (rho 267) (rho 272) (rho 277) (rho 282) (rho 287) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart56 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow280 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow281 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow282 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow283 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow284 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg56
  refine ⟨(rho 288), (rho 289), (rho 290), (rho 291), (rho 292), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc7, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc7Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc7Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc7, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc7Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc7Part1, choiceFreeAddAssoc] using h4

theorem template_part57_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart57 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) (rho 237) (rho 242) (rho 247) (rho 252) (rho 257) (rho 262) (rho 267) (rho 272) (rho 277) (rho 282) (rho 287) (rho 292) (rho 297)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg57 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) (rho 237) (rho 242) (rho 247) (rho 252) (rho 257) (rho 262) (rho 267) (rho 272) (rho 277) (rho 282) (rho 287) (rho 292) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart57 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow285 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow286 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow287 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow288 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow289 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg57
  refine ⟨(rho 293), (rho 294), (rho 295), (rho 296), (rho 297), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc8, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc8Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc8Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc8, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc8Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc8Part1, choiceFreeAddAssoc] using h4

theorem template_part58_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart58 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) (rho 237) (rho 242) (rho 247) (rho 252) (rho 257) (rho 262) (rho 267) (rho 272) (rho 277) (rho 282) (rho 287) (rho 292) (rho 297) (rho 302)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg58 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) (rho 237) (rho 242) (rho 247) (rho 252) (rho 257) (rho 262) (rho 267) (rho 272) (rho 277) (rho 282) (rho 287) (rho 292) (rho 297) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart58 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow290 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow291 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow292 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow293 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow294 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg58
  refine ⟨(rho 298), (rho 299), (rho 300), (rho 301), (rho 302), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc9, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc9Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc9Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc9, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc9Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc9Part1, choiceFreeAddAssoc] using h4

theorem template_part59_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart59 rho)
    {k : F → F → F → F → F → F → Prop} (hk : k (rho 282) (rho 287) (rho 292) (rho 297) (rho 302) (rho 307)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg59 (rho 97) (rho 102) (rho 107) (rho 112) (rho 117) (rho 122) (rho 127) (rho 132) (rho 137) (rho 142) (rho 147) (rho 152) (rho 157) (rho 162) (rho 167) (rho 172) (rho 177) (rho 182) (rho 187) (rho 192) (rho 197) (rho 202) (rho 207) (rho 212) (rho 217) (rho 222) (rho 227) (rho 232) (rho 237) (rho 242) (rho 247) (rho 252) (rho 257) (rho 262) (rho 267) (rho 272) (rho 277) (rho 282) (rho 287) (rho 292) (rho 297) (rho 302) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart59 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow295 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow296 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow297 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow298 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow299 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg59
  refine ⟨(rho 303), (rho 304), (rho 305), (rho 306), (rho 307), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc10, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc10Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc10Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc10, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc10Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationLc10Part1, choiceFreeAddAssoc] using h4

theorem template_part60_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart60 rho)
    {k : F → F → F → F → F → F → F → Prop} (hk : k (rho 282) (rho 287) (rho 292) (rho 297) (rho 302) (rho 307) (rho 312)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg60 (rho 282) (rho 287) (rho 292) (rho 297) (rho 302) (rho 307) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart60 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow300 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow301 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow302 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow303 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow304 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg60
  refine ⟨(rho 308), (rho 309), (rho 310), (rho 311), (rho 312), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part61_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart61 rho)
    {k : F → F → F → F → F → F → F → F → Prop} (hk : k (rho 282) (rho 287) (rho 292) (rho 297) (rho 302) (rho 307) (rho 312) (rho 317)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg61 (rho 282) (rho 287) (rho 292) (rho 297) (rho 302) (rho 307) (rho 312) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart61 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow305 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow306 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow307 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow308 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow309 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg61
  refine ⟨(rho 313), (rho 314), (rho 315), (rho 316), (rho 317), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part62_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart62 rho)
    {k : F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 282) (rho 287) (rho 292) (rho 297) (rho 302) (rho 307) (rho 312) (rho 317) (rho 322)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg62 (rho 282) (rho 287) (rho 292) (rho 297) (rho 302) (rho 307) (rho 312) (rho 317) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart62 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow310 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow311 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow312 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow313 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow314 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg62
  refine ⟨(rho 318), (rho 319), (rho 320), (rho 321), (rho 322), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part63_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart63 rho)
    {k : F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 282) (rho 287) (rho 292) (rho 297) (rho 302) (rho 307) (rho 312) (rho 317) (rho 322) (rho 327)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg63 (rho 282) (rho 287) (rho 292) (rho 297) (rho 302) (rho 307) (rho 312) (rho 317) (rho 322) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart63 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow315 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow316 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow317 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow318 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow319 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg63
  refine ⟨(rho 323), (rho 324), (rho 325), (rho 326), (rho 327), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part64_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart64 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 282) (rho 287) (rho 292) (rho 297) (rho 302) (rho 307) (rho 312) (rho 317) (rho 322) (rho 327) (rho 332)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg64 (rho 282) (rho 287) (rho 292) (rho 297) (rho 302) (rho 307) (rho 312) (rho 317) (rho 322) (rho 327) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart64 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow320 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow321 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow322 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow323 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow324 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg64
  refine ⟨(rho 328), (rho 329), (rho 330), (rho 331), (rho 332), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part65_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart65 rho)
    {k : F → F → F → F → F → F → Prop} (hk : k (rho 312) (rho 317) (rho 322) (rho 327) (rho 332) (rho 337)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg65 (rho 282) (rho 287) (rho 292) (rho 297) (rho 302) (rho 307) (rho 312) (rho 317) (rho 322) (rho 327) (rho 332) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart65 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow325 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow326 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow327 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow328 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow329 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg65
  refine ⟨(rho 333), (rho 334), (rho 335), (rho 336), (rho 337), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part66_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart66 rho)
    {k : F → F → F → F → F → F → F → Prop} (hk : k (rho 312) (rho 317) (rho 322) (rho 327) (rho 332) (rho 337) (rho 342)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg66 (rho 312) (rho 317) (rho 322) (rho 327) (rho 332) (rho 337) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart66 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow330 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow331 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow332 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow333 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow334 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg66
  refine ⟨(rho 338), (rho 339), (rho 340), (rho 341), (rho 342), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part67_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart67 rho)
    {k : F → F → F → F → F → F → F → F → Prop} (hk : k (rho 312) (rho 317) (rho 322) (rho 327) (rho 332) (rho 337) (rho 342) (rho 347)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg67 (rho 312) (rho 317) (rho 322) (rho 327) (rho 332) (rho 337) (rho 342) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart67 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow335 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow336 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow337 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow338 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow339 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg67
  refine ⟨(rho 343), (rho 344), (rho 345), (rho 346), (rho 347), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part68_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart68 rho)
    {k : F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 312) (rho 317) (rho 322) (rho 327) (rho 332) (rho 337) (rho 342) (rho 347) (rho 352)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg68 (rho 312) (rho 317) (rho 322) (rho 327) (rho 332) (rho 337) (rho 342) (rho 347) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart68 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow340 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow341 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow342 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow343 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow344 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg68
  refine ⟨(rho 348), (rho 349), (rho 350), (rho 351), (rho 352), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part69_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart69 rho)
    {k : F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 312) (rho 317) (rho 322) (rho 327) (rho 332) (rho 337) (rho 342) (rho 347) (rho 352) (rho 357)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg69 (rho 312) (rho 317) (rho 322) (rho 327) (rho 332) (rho 337) (rho 342) (rho 347) (rho 352) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart69 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow345 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow346 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow347 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow348 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow349 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg69
  refine ⟨(rho 353), (rho 354), (rho 355), (rho 356), (rho 357), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part70_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart70 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 312) (rho 317) (rho 322) (rho 327) (rho 332) (rho 337) (rho 342) (rho 347) (rho 352) (rho 357) (rho 362)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg70 (rho 312) (rho 317) (rho 322) (rho 327) (rho 332) (rho 337) (rho 342) (rho 347) (rho 352) (rho 357) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart70 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow350 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow351 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow352 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow353 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow354 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg70
  refine ⟨(rho 358), (rho 359), (rho 360), (rho 361), (rho 362), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part71_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart71 rho)
    {k : F → F → F → F → F → F → Prop} (hk : k (rho 342) (rho 347) (rho 352) (rho 357) (rho 362) (rho 367)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg71 (rho 312) (rho 317) (rho 322) (rho 327) (rho 332) (rho 337) (rho 342) (rho 347) (rho 352) (rho 357) (rho 362) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart71 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow355 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow356 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow357 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow358 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow359 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg71
  refine ⟨(rho 363), (rho 364), (rho 365), (rho 366), (rho 367), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part72_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart72 rho)
    {k : F → F → F → F → F → F → F → Prop} (hk : k (rho 342) (rho 347) (rho 352) (rho 357) (rho 362) (rho 367) (rho 372)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg72 (rho 342) (rho 347) (rho 352) (rho 357) (rho 362) (rho 367) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart72 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow360 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow361 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow362 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow363 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow364 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg72
  refine ⟨(rho 368), (rho 369), (rho 370), (rho 371), (rho 372), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part73_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart73 rho)
    {k : F → F → F → F → F → F → F → F → Prop} (hk : k (rho 342) (rho 347) (rho 352) (rho 357) (rho 362) (rho 367) (rho 372) (rho 377)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg73 (rho 342) (rho 347) (rho 352) (rho 357) (rho 362) (rho 367) (rho 372) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart73 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow365 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow366 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow367 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow368 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow369 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg73
  refine ⟨(rho 373), (rho 374), (rho 375), (rho 376), (rho 377), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part74_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart74 rho)
    {k : F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 342) (rho 347) (rho 352) (rho 357) (rho 362) (rho 367) (rho 372) (rho 377) (rho 382)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg74 (rho 342) (rho 347) (rho 352) (rho 357) (rho 362) (rho 367) (rho 372) (rho 377) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart74 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow370 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow371 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow372 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow373 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow374 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg74
  refine ⟨(rho 378), (rho 379), (rho 380), (rho 381), (rho 382), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part75_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart75 rho)
    {k : F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 342) (rho 347) (rho 352) (rho 357) (rho 362) (rho 367) (rho 372) (rho 377) (rho 382) (rho 387)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg75 (rho 342) (rho 347) (rho 352) (rho 357) (rho 362) (rho 367) (rho 372) (rho 377) (rho 382) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart75 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow375 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow376 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow377 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow378 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow379 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg75
  refine ⟨(rho 383), (rho 384), (rho 385), (rho 386), (rho 387), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part76_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart76 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 342) (rho 347) (rho 352) (rho 357) (rho 362) (rho 367) (rho 372) (rho 377) (rho 382) (rho 387) (rho 392)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg76 (rho 342) (rho 347) (rho 352) (rho 357) (rho 362) (rho 367) (rho 372) (rho 377) (rho 382) (rho 387) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart76 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow380 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow381 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow382 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow383 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow384 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg76
  refine ⟨(rho 388), (rho 389), (rho 390), (rho 391), (rho 392), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part77_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart77 rho)
    {k : F → F → F → F → F → F → Prop} (hk : k (rho 372) (rho 377) (rho 382) (rho 387) (rho 392) (rho 397)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg77 (rho 342) (rho 347) (rho 352) (rho 357) (rho 362) (rho 367) (rho 372) (rho 377) (rho 382) (rho 387) (rho 392) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationPart77 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow385 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow386 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow387 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow388 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relationRow389 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.seg77
  refine ⟨(rho 393), (rho 394), (rho 395), (rho 396), (rho 397), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
theorem template_relation_to_poseidon
    (rho : Nat → F) (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relation rho) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.relation (rho 1) (rho 2) (rho 8) (rho 9) (rho 15) (rho 21) (rho 27)
      (fun w372 w377 w382 w387 w392 w397 => w372 = rho 372 ∧ w377 = rho 377 ∧ w382 = rho 382 ∧ w387 = rho 387 ∧ w392 = rho 392 ∧ w397 = rho 397) := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relation at h
  rcases h with ⟨
    p0, p1, p2, p3, p4, p5, p6, p7,
    p8, p9, p10, p11, p12, p13, p14, p15,
    p16, p17, p18, p19, p20, p21, p22, p23,
    p24, p25, p26, p27, p28, p29, p30, p31,
    p32, p33, p34, p35, p36, p37, p38, p39,
    p40, p41, p42, p43, p44, p45, p46, p47,
    p48, p49, p50, p51, p52, p53, p54, p55,
    p56, p57, p58, p59, p60, p61, p62, p63,
    p64, p65, p66, p67, p68, p69, p70, p71,
    p72, p73, p74, p75, p76, p77
  ⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34PoseidonRows390.relation
  apply template_part0_to_extracted rho p0
  apply template_part1_to_extracted rho p1
  apply template_part2_to_extracted rho p2
  apply template_part3_to_extracted rho p3
  apply template_part4_to_extracted rho p4
  apply template_part5_to_extracted rho p5
  apply template_part6_to_extracted rho p6
  apply template_part7_to_extracted rho p7
  apply template_part8_to_extracted rho p8
  apply template_part9_to_extracted rho p9
  apply template_part10_to_extracted rho p10
  apply template_part11_to_extracted rho p11
  apply template_part12_to_extracted rho p12
  apply template_part13_to_extracted rho p13
  apply template_part14_to_extracted rho p14
  apply template_part15_to_extracted rho p15
  apply template_part16_to_extracted rho p16
  apply template_part17_to_extracted rho p17
  apply template_part18_to_extracted rho p18
  apply template_part19_to_extracted rho p19
  apply template_part20_to_extracted rho p20
  apply template_part21_to_extracted rho p21
  apply template_part22_to_extracted rho p22
  apply template_part23_to_extracted rho p23
  apply template_part24_to_extracted rho p24
  apply template_part25_to_extracted rho p25
  apply template_part26_to_extracted rho p26
  apply template_part27_to_extracted rho p27
  apply template_part28_to_extracted rho p28
  apply template_part29_to_extracted rho p29
  apply template_part30_to_extracted rho p30
  apply template_part31_to_extracted rho p31
  apply template_part32_to_extracted rho p32
  apply template_part33_to_extracted rho p33
  apply template_part34_to_extracted rho p34
  apply template_part35_to_extracted rho p35
  apply template_part36_to_extracted rho p36
  apply template_part37_to_extracted rho p37
  apply template_part38_to_extracted rho p38
  apply template_part39_to_extracted rho p39
  apply template_part40_to_extracted rho p40
  apply template_part41_to_extracted rho p41
  apply template_part42_to_extracted rho p42
  apply template_part43_to_extracted rho p43
  apply template_part44_to_extracted rho p44
  apply template_part45_to_extracted rho p45
  apply template_part46_to_extracted rho p46
  apply template_part47_to_extracted rho p47
  apply template_part48_to_extracted rho p48
  apply template_part49_to_extracted rho p49
  apply template_part50_to_extracted rho p50
  apply template_part51_to_extracted rho p51
  apply template_part52_to_extracted rho p52
  apply template_part53_to_extracted rho p53
  apply template_part54_to_extracted rho p54
  apply template_part55_to_extracted rho p55
  apply template_part56_to_extracted rho p56
  apply template_part57_to_extracted rho p57
  apply template_part58_to_extracted rho p58
  apply template_part59_to_extracted rho p59
  apply template_part60_to_extracted rho p60
  apply template_part61_to_extracted rho p61
  apply template_part62_to_extracted rho p62
  apply template_part63_to_extracted rho p63
  apply template_part64_to_extracted rho p64
  apply template_part65_to_extracted rho p65
  apply template_part66_to_extracted rho p66
  apply template_part67_to_extracted rho p67
  apply template_part68_to_extracted rho p68
  apply template_part69_to_extracted rho p69
  apply template_part70_to_extracted rho p70
  apply template_part71_to_extracted rho p71
  apply template_part72_to_extracted rho p72
  apply template_part73_to_extracted rho p73
  apply template_part74_to_extracted rho p74
  apply template_part75_to_extracted rho p75
  apply template_part76_to_extracted rho p76
  apply template_part77_to_extracted rho p77
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sound (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec.relation rho) : spec rho := by
  have hExtracted := template_relation_to_poseidon rho h
  rcases Shieldd.GnarkFormal.Deployed.CertifiedGadgetComplianceLeaf_e42e4a59ca34Poseidon.relation_sound_permSpec
      (rho 1) (rho 2) (rho 8) (rho 9) (rho 15) (rho 21) (rho 27) _ hExtracted with
    ⟨w372, w377, w382, w387, w392, w397, hk, hperm⟩
  rcases hk with ⟨hw372, hw377, hw382, hw387, hw392, hw397⟩
  unfold spec output
  rw [← hw372, ← hw377, ← hw382, ← hw387, ← hw392, ← hw397]
  exact hperm


end Shieldd.GnarkFormal.Deployed.Templates.Semantics.TGadgetComplianceLeaf_e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec
