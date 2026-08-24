import ShielddGnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e
import ShielddGnarkFormal.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0Poseidon.SemanticBridge
import ShielddGnarkFormal.Deployed.PrimeOrder
import Mathlib.Tactic.LinearCombination

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

namespace Shieldd.GnarkFormal.Deployed.Templates.Semantics.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e

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
  Shieldd.GnarkFormal.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0Poseidon.s38_1 (rho 299) (rho 304) (rho 309) (rho 314)

def spec (rho : Nat → F) : Prop :=
  output rho =
    Shieldd.GnarkFormal.Poseidon3Bridge.permSpec3
      (3064133732739839324562890722780110204743400790580066376892340142513796818031 : F)
      ((-1 : F) * rho 1 + rho 2) (rho 8) (rho 14)

theorem template_part0_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart0 rho)
    {k : F → F → F → Prop} (hk : k (rho 8) (rho 14) (rho 7)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg0 (rho 1) (rho 2) (rho 8) (rho 14) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart0 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow0 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow1 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow2 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow3 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow4 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg0
  refine ⟨(rho 3), (rho 4), (rho 5), (rho 6), (rho 7), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part1_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart1 rho)
    {k : F → F → F → Prop} (hk : k (rho 7) (rho 14) (rho 13)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg1 (rho 7) (rho 8) (rho 14) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart1 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow5 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow6 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow7 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow8 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow9 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg1
  refine ⟨(rho 9), (rho 10), (rho 11), (rho 12), (rho 13), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part2_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart2 rho)
    {k : F → F → F → Prop} (hk : k (rho 7) (rho 13) (rho 19)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg2 (rho 7) (rho 13) (rho 14) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart2 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow10 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow11 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow12 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow13 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow14 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg2
  refine ⟨(rho 15), (rho 16), (rho 17), (rho 18), (rho 19), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part3_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart3 rho)
    {k : F → F → F → F → Prop} (hk : k (rho 7) (rho 13) (rho 19) (rho 24)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg3 (rho 7) (rho 13) (rho 19) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart3 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow15 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow16 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow17 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow18 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow19 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg3
  refine ⟨(rho 20), (rho 21), (rho 22), (rho 23), (rho 24), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part4_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart4 rho)
    {k : F → F → F → F → F → Prop} (hk : k (rho 7) (rho 13) (rho 19) (rho 24) (rho 29)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg4 (rho 7) (rho 13) (rho 19) (rho 24) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart4 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow20 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow21 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow22 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow23 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow24 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg4
  refine ⟨(rho 25), (rho 26), (rho 27), (rho 28), (rho 29), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part5_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart5 rho)
    {k : F → F → F → F → F → F → Prop} (hk : k (rho 7) (rho 13) (rho 19) (rho 24) (rho 29) (rho 34)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg5 (rho 7) (rho 13) (rho 19) (rho 24) (rho 29) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart5 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow25 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow26 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow27 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow28 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow29 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg5
  refine ⟨(rho 30), (rho 31), (rho 32), (rho 33), (rho 34), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part6_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart6 rho)
    {k : F → F → F → F → Prop} (hk : k (rho 24) (rho 29) (rho 34) (rho 39)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg6 (rho 7) (rho 13) (rho 19) (rho 24) (rho 29) (rho 34) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart6 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow30 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow31 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow32 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow33 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow34 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg6
  refine ⟨(rho 35), (rho 36), (rho 37), (rho 38), (rho 39), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part7_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart7 rho)
    {k : F → F → F → F → F → Prop} (hk : k (rho 24) (rho 29) (rho 34) (rho 39) (rho 44)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg7 (rho 24) (rho 29) (rho 34) (rho 39) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart7 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow35 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow36 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow37 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow38 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow39 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg7
  refine ⟨(rho 40), (rho 41), (rho 42), (rho 43), (rho 44), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part8_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart8 rho)
    {k : F → F → F → F → F → F → Prop} (hk : k (rho 24) (rho 29) (rho 34) (rho 39) (rho 44) (rho 49)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg8 (rho 24) (rho 29) (rho 34) (rho 39) (rho 44) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart8 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow40 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow41 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow42 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow43 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow44 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg8
  refine ⟨(rho 45), (rho 46), (rho 47), (rho 48), (rho 49), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part9_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart9 rho)
    {k : F → F → F → F → F → F → F → Prop} (hk : k (rho 24) (rho 29) (rho 34) (rho 39) (rho 44) (rho 49) (rho 54)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg9 (rho 24) (rho 29) (rho 34) (rho 39) (rho 44) (rho 49) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart9 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow45 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow46 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow47 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow48 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow49 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg9
  refine ⟨(rho 50), (rho 51), (rho 52), (rho 53), (rho 54), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part10_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart10 rho)
    {k : F → F → F → F → Prop} (hk : k (rho 44) (rho 49) (rho 54) (rho 59)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg10 (rho 24) (rho 29) (rho 34) (rho 39) (rho 44) (rho 49) (rho 54) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart10 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow50 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow51 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow52 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow53 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow54 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg10
  refine ⟨(rho 55), (rho 56), (rho 57), (rho 58), (rho 59), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part11_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart11 rho)
    {k : F → F → F → F → F → Prop} (hk : k (rho 44) (rho 49) (rho 54) (rho 59) (rho 64)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg11 (rho 44) (rho 49) (rho 54) (rho 59) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart11 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow55 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow56 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow57 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow58 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow59 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg11
  refine ⟨(rho 60), (rho 61), (rho 62), (rho 63), (rho 64), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part12_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart12 rho)
    {k : F → F → F → F → F → F → Prop} (hk : k (rho 44) (rho 49) (rho 54) (rho 59) (rho 64) (rho 69)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg12 (rho 44) (rho 49) (rho 54) (rho 59) (rho 64) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart12 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow60 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow61 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow62 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow63 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow64 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg12
  refine ⟨(rho 65), (rho 66), (rho 67), (rho 68), (rho 69), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part13_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart13 rho)
    {k : F → F → F → F → F → F → F → Prop} (hk : k (rho 44) (rho 49) (rho 54) (rho 59) (rho 64) (rho 69) (rho 74)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg13 (rho 44) (rho 49) (rho 54) (rho 59) (rho 64) (rho 69) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart13 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow65 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow66 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow67 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow68 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow69 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg13
  refine ⟨(rho 70), (rho 71), (rho 72), (rho 73), (rho 74), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part14_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart14 rho)
    {k : F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg14 (rho 44) (rho 49) (rho 54) (rho 59) (rho 64) (rho 69) (rho 74) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart14 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow70 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow71 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow72 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow73 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow74 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg14
  refine ⟨(rho 75), (rho 76), (rho 77), (rho 78), (rho 79), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part15_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart15 rho)
    {k : F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg15 (rho 64) (rho 69) (rho 74) (rho 79) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart15 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow75 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow76 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow77 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow78 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow79 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg15
  refine ⟨(rho 80), (rho 81), (rho 82), (rho 83), (rho 84), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part16_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart16 rho)
    {k : F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg16 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart16 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow80 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow81 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow82 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow83 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow84 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg16
  refine ⟨(rho 85), (rho 86), (rho 87), (rho 88), (rho 89), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part17_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart17 rho)
    {k : F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg17 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart17 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow85 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow86 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow87 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow88 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow89 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg17
  refine ⟨(rho 90), (rho 91), (rho 92), (rho 93), (rho 94), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part18_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart18 rho)
    {k : F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg18 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart18 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow90 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow91 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow92 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow93 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow94 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg18
  refine ⟨(rho 95), (rho 96), (rho 97), (rho 98), (rho 99), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part19_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart19 rho)
    {k : F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg19 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart19 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow95 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow96 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow97 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow98 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow99 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg19
  refine ⟨(rho 100), (rho 101), (rho 102), (rho 103), (rho 104), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part20_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart20 rho)
    {k : F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg20 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart20 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow100 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow101 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow102 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow103 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow104 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg20
  refine ⟨(rho 105), (rho 106), (rho 107), (rho 108), (rho 109), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part21_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart21 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg21 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart21 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow105 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow106 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow107 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow108 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow109 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg21
  refine ⟨(rho 110), (rho 111), (rho 112), (rho 113), (rho 114), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part22_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart22 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg22 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart22 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow110 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow111 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow112 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow113 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow114 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg22
  refine ⟨(rho 115), (rho 116), (rho 117), (rho 118), (rho 119), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part23_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart23 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg23 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart23 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow115 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow116 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow117 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow118 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow119 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg23
  refine ⟨(rho 120), (rho 121), (rho 122), (rho 123), (rho 124), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part24_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart24 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg24 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart24 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow120 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow121 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow122 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow123 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow124 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg24
  refine ⟨(rho 125), (rho 126), (rho 127), (rho 128), (rho 129), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part25_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart25 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg25 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart25 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow125 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow126 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow127 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow128 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow129 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg25
  refine ⟨(rho 130), (rho 131), (rho 132), (rho 133), (rho 134), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part26_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart26 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg26 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart26 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow130 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow131 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow132 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow133 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow134 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg26
  refine ⟨(rho 135), (rho 136), (rho 137), (rho 138), (rho 139), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part27_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart27 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg27 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart27 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow135 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow136 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow137 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow138 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow139 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg27
  refine ⟨(rho 140), (rho 141), (rho 142), (rho 143), (rho 144), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part28_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart28 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg28 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart28 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow140 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow141 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow142 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow143 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow144 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg28
  refine ⟨(rho 145), (rho 146), (rho 147), (rho 148), (rho 149), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part29_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart29 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg29 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart29 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow145 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow146 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow147 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow148 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow149 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg29
  refine ⟨(rho 150), (rho 151), (rho 152), (rho 153), (rho 154), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part30_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart30 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg30 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart30 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow150 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow151 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow152 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow153 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow154 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg30
  refine ⟨(rho 155), (rho 156), (rho 157), (rho 158), (rho 159), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part31_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart31 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg31 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart31 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow155 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow156 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow157 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow158 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow159 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg31
  refine ⟨(rho 160), (rho 161), (rho 162), (rho 163), (rho 164), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part32_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart32 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg32 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart32 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow160 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow161 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow162 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow163 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow164 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg32
  refine ⟨(rho 165), (rho 166), (rho 167), (rho 168), (rho 169), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part33_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart33 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg33 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart33 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow165 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow166 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow167 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow168 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow169 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg33
  refine ⟨(rho 170), (rho 171), (rho 172), (rho 173), (rho 174), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part34_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart34 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg34 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart34 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow170 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow171 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow172 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow173 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow174 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg34
  refine ⟨(rho 175), (rho 176), (rho 177), (rho 178), (rho 179), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part35_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart35 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) (rho 184)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg35 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart35 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow175 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow176 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow177 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow178 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow179 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg35
  refine ⟨(rho 180), (rho 181), (rho 182), (rho 183), (rho 184), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part36_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart36 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) (rho 184) (rho 189)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg36 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) (rho 184) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart36 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow180 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow181 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow182 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow183 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow184 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg36
  refine ⟨(rho 185), (rho 186), (rho 187), (rho 188), (rho 189), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part37_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart37 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) (rho 184) (rho 189) (rho 194)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg37 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) (rho 184) (rho 189) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart37 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow185 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow186 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow187 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow188 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow189 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg37
  refine ⟨(rho 190), (rho 191), (rho 192), (rho 193), (rho 194), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part38_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart38 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) (rho 184) (rho 189) (rho 194) (rho 199)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg38 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) (rho 184) (rho 189) (rho 194) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart38 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow190 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow191 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow192 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow193 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow194 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg38
  refine ⟨(rho 195), (rho 196), (rho 197), (rho 198), (rho 199), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part39_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart39 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) (rho 184) (rho 189) (rho 194) (rho 199) (rho 204)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg39 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) (rho 184) (rho 189) (rho 194) (rho 199) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart39 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow195 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow196 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow197 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow198 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow199 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg39
  refine ⟨(rho 200), (rho 201), (rho 202), (rho 203), (rho 204), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part40_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart40 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) (rho 184) (rho 189) (rho 194) (rho 199) (rho 204) (rho 209)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg40 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) (rho 184) (rho 189) (rho 194) (rho 199) (rho 204) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart40 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow200 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow201 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow202 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow203 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow204 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg40
  refine ⟨(rho 205), (rho 206), (rho 207), (rho 208), (rho 209), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part41_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart41 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) (rho 184) (rho 189) (rho 194) (rho 199) (rho 204) (rho 209) (rho 214)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg41 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) (rho 184) (rho 189) (rho 194) (rho 199) (rho 204) (rho 209) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart41 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow205 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow206 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow207 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow208 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow209 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg41
  refine ⟨(rho 210), (rho 211), (rho 212), (rho 213), (rho 214), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part42_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart42 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) (rho 184) (rho 189) (rho 194) (rho 199) (rho 204) (rho 209) (rho 214) (rho 219)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg42 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) (rho 184) (rho 189) (rho 194) (rho 199) (rho 204) (rho 209) (rho 214) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart42 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow210 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow211 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow212 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow213 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow214 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg42
  refine ⟨(rho 215), (rho 216), (rho 217), (rho 218), (rho 219), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part43_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart43 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) (rho 184) (rho 189) (rho 194) (rho 199) (rho 204) (rho 209) (rho 214) (rho 219) (rho 224)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg43 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) (rho 184) (rho 189) (rho 194) (rho 199) (rho 204) (rho 209) (rho 214) (rho 219) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart43 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow215 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow216 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow217 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow218 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow219 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg43
  refine ⟨(rho 220), (rho 221), (rho 222), (rho 223), (rho 224), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc0Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc0Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc0Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc0Part1, choiceFreeAddAssoc] using h4

theorem template_part44_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart44 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) (rho 184) (rho 189) (rho 194) (rho 199) (rho 204) (rho 209) (rho 214) (rho 219) (rho 224) (rho 229)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg44 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) (rho 184) (rho 189) (rho 194) (rho 199) (rho 204) (rho 209) (rho 214) (rho 219) (rho 224) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart44 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow220 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow221 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow222 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow223 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow224 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg44
  refine ⟨(rho 225), (rho 226), (rho 227), (rho 228), (rho 229), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc1, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc1Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc1Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc1, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc1Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc1Part1, choiceFreeAddAssoc] using h4

theorem template_part45_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart45 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) (rho 184) (rho 189) (rho 194) (rho 199) (rho 204) (rho 209) (rho 214) (rho 219) (rho 224) (rho 229) (rho 234)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg45 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) (rho 184) (rho 189) (rho 194) (rho 199) (rho 204) (rho 209) (rho 214) (rho 219) (rho 224) (rho 229) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart45 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow225 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow226 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow227 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow228 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow229 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg45
  refine ⟨(rho 230), (rho 231), (rho 232), (rho 233), (rho 234), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc2, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc2Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc2Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc2, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc2Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc2Part1, choiceFreeAddAssoc] using h4

theorem template_part46_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart46 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) (rho 184) (rho 189) (rho 194) (rho 199) (rho 204) (rho 209) (rho 214) (rho 219) (rho 224) (rho 229) (rho 234) (rho 239)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg46 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) (rho 184) (rho 189) (rho 194) (rho 199) (rho 204) (rho 209) (rho 214) (rho 219) (rho 224) (rho 229) (rho 234) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart46 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow230 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow231 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow232 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow233 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow234 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg46
  refine ⟨(rho 235), (rho 236), (rho 237), (rho 238), (rho 239), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc3, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc3Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc3Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc3, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc3Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc3Part1, choiceFreeAddAssoc] using h4

theorem template_part47_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart47 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) (rho 184) (rho 189) (rho 194) (rho 199) (rho 204) (rho 209) (rho 214) (rho 219) (rho 224) (rho 229) (rho 234) (rho 239) (rho 244)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg47 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) (rho 184) (rho 189) (rho 194) (rho 199) (rho 204) (rho 209) (rho 214) (rho 219) (rho 224) (rho 229) (rho 234) (rho 239) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart47 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow235 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow236 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow237 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow238 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow239 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg47
  refine ⟨(rho 240), (rho 241), (rho 242), (rho 243), (rho 244), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc4, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc4Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc4Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc4, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc4Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc4Part1, choiceFreeAddAssoc] using h4

theorem template_part48_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart48 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) (rho 184) (rho 189) (rho 194) (rho 199) (rho 204) (rho 209) (rho 214) (rho 219) (rho 224) (rho 229) (rho 234) (rho 239) (rho 244) (rho 249)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg48 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) (rho 184) (rho 189) (rho 194) (rho 199) (rho 204) (rho 209) (rho 214) (rho 219) (rho 224) (rho 229) (rho 234) (rho 239) (rho 244) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart48 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow240 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow241 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow242 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow243 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow244 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg48
  refine ⟨(rho 245), (rho 246), (rho 247), (rho 248), (rho 249), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc5, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc5Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc5Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc5, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc5Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc5Part1, choiceFreeAddAssoc] using h4

theorem template_part49_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart49 rho)
    {k : F → F → F → F → Prop} (hk : k (rho 239) (rho 244) (rho 249) (rho 254)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg49 (rho 64) (rho 69) (rho 74) (rho 79) (rho 84) (rho 89) (rho 94) (rho 99) (rho 104) (rho 109) (rho 114) (rho 119) (rho 124) (rho 129) (rho 134) (rho 139) (rho 144) (rho 149) (rho 154) (rho 159) (rho 164) (rho 169) (rho 174) (rho 179) (rho 184) (rho 189) (rho 194) (rho 199) (rho 204) (rho 209) (rho 214) (rho 219) (rho 224) (rho 229) (rho 234) (rho 239) (rho 244) (rho 249) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart49 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow245 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow246 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow247 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow248 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow249 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg49
  refine ⟨(rho 250), (rho 251), (rho 252), (rho 253), (rho 254), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc6, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc6Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc6Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc6, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc6Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationLc6Part1, choiceFreeAddAssoc] using h4

theorem template_part50_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart50 rho)
    {k : F → F → F → F → F → Prop} (hk : k (rho 239) (rho 244) (rho 249) (rho 254) (rho 259)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg50 (rho 239) (rho 244) (rho 249) (rho 254) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart50 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow250 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow251 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow252 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow253 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow254 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg50
  refine ⟨(rho 255), (rho 256), (rho 257), (rho 258), (rho 259), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part51_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart51 rho)
    {k : F → F → F → F → F → F → Prop} (hk : k (rho 239) (rho 244) (rho 249) (rho 254) (rho 259) (rho 264)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg51 (rho 239) (rho 244) (rho 249) (rho 254) (rho 259) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart51 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow255 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow256 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow257 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow258 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow259 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg51
  refine ⟨(rho 260), (rho 261), (rho 262), (rho 263), (rho 264), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part52_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart52 rho)
    {k : F → F → F → F → F → F → F → Prop} (hk : k (rho 239) (rho 244) (rho 249) (rho 254) (rho 259) (rho 264) (rho 269)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg52 (rho 239) (rho 244) (rho 249) (rho 254) (rho 259) (rho 264) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart52 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow260 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow261 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow262 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow263 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow264 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg52
  refine ⟨(rho 265), (rho 266), (rho 267), (rho 268), (rho 269), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part53_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart53 rho)
    {k : F → F → F → F → Prop} (hk : k (rho 259) (rho 264) (rho 269) (rho 274)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg53 (rho 239) (rho 244) (rho 249) (rho 254) (rho 259) (rho 264) (rho 269) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart53 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow265 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow266 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow267 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow268 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow269 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg53
  refine ⟨(rho 270), (rho 271), (rho 272), (rho 273), (rho 274), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part54_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart54 rho)
    {k : F → F → F → F → F → Prop} (hk : k (rho 259) (rho 264) (rho 269) (rho 274) (rho 279)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg54 (rho 259) (rho 264) (rho 269) (rho 274) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart54 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow270 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow271 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow272 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow273 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow274 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg54
  refine ⟨(rho 275), (rho 276), (rho 277), (rho 278), (rho 279), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part55_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart55 rho)
    {k : F → F → F → F → F → F → Prop} (hk : k (rho 259) (rho 264) (rho 269) (rho 274) (rho 279) (rho 284)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg55 (rho 259) (rho 264) (rho 269) (rho 274) (rho 279) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart55 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow275 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow276 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow277 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow278 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow279 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg55
  refine ⟨(rho 280), (rho 281), (rho 282), (rho 283), (rho 284), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part56_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart56 rho)
    {k : F → F → F → F → F → F → F → Prop} (hk : k (rho 259) (rho 264) (rho 269) (rho 274) (rho 279) (rho 284) (rho 289)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg56 (rho 259) (rho 264) (rho 269) (rho 274) (rho 279) (rho 284) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart56 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow280 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow281 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow282 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow283 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow284 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg56
  refine ⟨(rho 285), (rho 286), (rho 287), (rho 288), (rho 289), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part57_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart57 rho)
    {k : F → F → F → F → Prop} (hk : k (rho 279) (rho 284) (rho 289) (rho 294)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg57 (rho 259) (rho 264) (rho 269) (rho 274) (rho 279) (rho 284) (rho 289) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart57 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow285 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow286 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow287 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow288 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow289 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg57
  refine ⟨(rho 290), (rho 291), (rho 292), (rho 293), (rho 294), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part58_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart58 rho)
    {k : F → F → F → F → F → Prop} (hk : k (rho 279) (rho 284) (rho 289) (rho 294) (rho 299)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg58 (rho 279) (rho 284) (rho 289) (rho 294) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart58 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow290 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow291 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow292 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow293 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow294 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg58
  refine ⟨(rho 295), (rho 296), (rho 297), (rho 298), (rho 299), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part59_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart59 rho)
    {k : F → F → F → F → F → F → Prop} (hk : k (rho 279) (rho 284) (rho 289) (rho 294) (rho 299) (rho 304)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg59 (rho 279) (rho 284) (rho 289) (rho 294) (rho 299) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart59 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow295 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow296 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow297 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow298 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow299 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg59
  refine ⟨(rho 300), (rho 301), (rho 302), (rho 303), (rho 304), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part60_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart60 rho)
    {k : F → F → F → F → F → F → F → Prop} (hk : k (rho 279) (rho 284) (rho 289) (rho 294) (rho 299) (rho 304) (rho 309)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg60 (rho 279) (rho 284) (rho 289) (rho 294) (rho 299) (rho 304) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart60 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow300 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow301 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow302 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow303 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow304 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg60
  refine ⟨(rho 305), (rho 306), (rho 307), (rho 308), (rho 309), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part61_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart61 rho)
    {k : F → F → F → F → Prop} (hk : k (rho 299) (rho 304) (rho 309) (rho 314)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg61 (rho 279) (rho 284) (rho 289) (rho 294) (rho 299) (rho 304) (rho 309) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationPart61 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow305 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow306 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow307 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow308 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relationRow309 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg61
  refine ⟨(rho 310), (rho 311), (rho 312), (rho 313), (rho 314), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
theorem template_relation_to_poseidon
    (rho : Nat → F) (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relation rho) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.relation (rho 1) (rho 2) (rho 8) (rho 14)
      (fun w299 w304 w309 w314 => w299 = rho 299 ∧ w304 = rho 304 ∧ w309 = rho 309 ∧ w314 = rho 314) := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relation at h
  rcases h with ⟨
    p0, p1, p2, p3, p4, p5, p6, p7,
    p8, p9, p10, p11, p12, p13, p14, p15,
    p16, p17, p18, p19, p20, p21, p22, p23,
    p24, p25, p26, p27, p28, p29, p30, p31,
    p32, p33, p34, p35, p36, p37, p38, p39,
    p40, p41, p42, p43, p44, p45, p46, p47,
    p48, p49, p50, p51, p52, p53, p54, p55,
    p56, p57, p58, p59, p60, p61
  ⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.relation
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
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem sound (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e.relation rho) : spec rho := by
  have hExtracted := template_relation_to_poseidon rho h
  rcases Shieldd.GnarkFormal.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0Poseidon.relation_sound_permSpec
      (rho 1) (rho 2) (rho 8) (rho 14) _ hExtracted with
    ⟨w299, w304, w309, w314, hk, hperm⟩
  rcases hk with ⟨hw299, hw304, hw309, hw314⟩
  unfold spec output
  rw [← hw299, ← hw304, ← hw309, ← hw314]
  exact hperm


end Shieldd.GnarkFormal.Deployed.Templates.Semantics.TGadgetAssetRegistryParamsHash_1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e
