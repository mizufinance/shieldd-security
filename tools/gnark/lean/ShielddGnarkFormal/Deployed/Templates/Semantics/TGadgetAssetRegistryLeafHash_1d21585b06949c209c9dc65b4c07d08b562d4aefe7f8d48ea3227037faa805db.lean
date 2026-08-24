import ShielddGnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db
import ShielddGnarkFormal.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694Poseidon.SemanticBridge
import ShielddGnarkFormal.Deployed.PrimeOrder
import Mathlib.Tactic.LinearCombination

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

namespace Shieldd.GnarkFormal.Deployed.Templates.Semantics.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db

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
  Shieldd.GnarkFormal.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694Poseidon.s38_1 (rho 378) (rho 383) (rho 388) (rho 393) (rho 398) (rho 403)

def spec (rho : Nat → F) : Prop :=
  output rho =
    Shieldd.GnarkFormal.Poseidon5Bridge.permSpec5
      (7414146286439358428123110060125696348906971675449116418017868010797147357618 : F)
      (rho 1) (rho 7) (rho 13) ((6755569399542696339399059951025237225100719468123251062348186764733927391233 : F) * rho 19 + (7037051457856975353540687448984622109479916112628386523279361213264507699201 : F) * rho 20 + (7238110070938603220784707090384182741179342287274911852515914390786350776321 : F) * rho 21 + (7388904030749824121217721821433853214953911918259805849443329273927733084161 : F) * rho 22) ((7238110070938603220784707090384182741179342287274911852515914390786350776321 : F) * rho 28 + (7388904030749824121217721821433853214953911918259805849443329273927733084161 : F) * rho 29 + (4691367638571316902360458299323081406319944075085591015519574142176338466134 : F) * rho 30 + (7600015574485533381823942444903391878238309401638657445141710110325668315137 : F) * rho 31 + (2303035022571373752067861346940421781284336182314744680345972760704747974284 : F) * rho 32 + (7740756603642672888894756193883084320427907723891225175607297334590958469121 : F) * rho 33)

theorem template_part0_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart0 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 7) (rho 13) (rho 19) (rho 20) (rho 21) (rho 22) (rho 28) (rho 29) (rho 30) (rho 31) (rho 32) (rho 33) (rho 6)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg0 (rho 1) (rho 7) (rho 13) (rho 19) (rho 20) (rho 21) (rho 22) (rho 28) (rho 29) (rho 30) (rho 31) (rho 32) (rho 33) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart0 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow0 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow1 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow2 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow3 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow4 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg0
  refine ⟨(rho 2), (rho 3), (rho 4), (rho 5), (rho 6), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part1_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart1 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 6) (rho 13) (rho 19) (rho 20) (rho 21) (rho 22) (rho 28) (rho 29) (rho 30) (rho 31) (rho 32) (rho 33) (rho 12)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg1 (rho 6) (rho 7) (rho 13) (rho 19) (rho 20) (rho 21) (rho 22) (rho 28) (rho 29) (rho 30) (rho 31) (rho 32) (rho 33) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart1 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow5 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow6 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow7 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow8 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow9 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg1
  refine ⟨(rho 8), (rho 9), (rho 10), (rho 11), (rho 12), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part2_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart2 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 6) (rho 12) (rho 19) (rho 20) (rho 21) (rho 22) (rho 28) (rho 29) (rho 30) (rho 31) (rho 32) (rho 33) (rho 18)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg2 (rho 6) (rho 12) (rho 13) (rho 19) (rho 20) (rho 21) (rho 22) (rho 28) (rho 29) (rho 30) (rho 31) (rho 32) (rho 33) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart2 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow10 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow11 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow12 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow13 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow14 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg2
  refine ⟨(rho 14), (rho 15), (rho 16), (rho 17), (rho 18), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part3_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart3 rho)
    {k : F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 6) (rho 12) (rho 18) (rho 28) (rho 29) (rho 30) (rho 31) (rho 32) (rho 33) (rho 27)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg3 (rho 6) (rho 12) (rho 18) (rho 19) (rho 20) (rho 21) (rho 22) (rho 28) (rho 29) (rho 30) (rho 31) (rho 32) (rho 33) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart3 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow15 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow16 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow17 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow18 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow19 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg3
  refine ⟨(rho 23), (rho 24), (rho 25), (rho 26), (rho 27), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part4_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart4 rho)
    {k : F → F → F → F → F → Prop} (hk : k (rho 6) (rho 12) (rho 18) (rho 27) (rho 38)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg4 (rho 6) (rho 12) (rho 18) (rho 27) (rho 28) (rho 29) (rho 30) (rho 31) (rho 32) (rho 33) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart4 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow20 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow21 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow22 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow23 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow24 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg4
  refine ⟨(rho 34), (rho 35), (rho 36), (rho 37), (rho 38), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part5_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart5 rho)
    {k : F → F → F → F → F → F → Prop} (hk : k (rho 6) (rho 12) (rho 18) (rho 27) (rho 38) (rho 43)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg5 (rho 6) (rho 12) (rho 18) (rho 27) (rho 38) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart5 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow25 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow26 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow27 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow28 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow29 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg5
  refine ⟨(rho 39), (rho 40), (rho 41), (rho 42), (rho 43), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part6_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart6 rho)
    {k : F → F → F → F → F → F → F → Prop} (hk : k (rho 6) (rho 12) (rho 18) (rho 27) (rho 38) (rho 43) (rho 48)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg6 (rho 6) (rho 12) (rho 18) (rho 27) (rho 38) (rho 43) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart6 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow30 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow31 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow32 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow33 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow34 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg6
  refine ⟨(rho 44), (rho 45), (rho 46), (rho 47), (rho 48), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part7_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart7 rho)
    {k : F → F → F → F → F → F → F → F → Prop} (hk : k (rho 6) (rho 12) (rho 18) (rho 27) (rho 38) (rho 43) (rho 48) (rho 53)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg7 (rho 6) (rho 12) (rho 18) (rho 27) (rho 38) (rho 43) (rho 48) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart7 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow35 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow36 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow37 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow38 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow39 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg7
  refine ⟨(rho 49), (rho 50), (rho 51), (rho 52), (rho 53), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part8_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart8 rho)
    {k : F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 6) (rho 12) (rho 18) (rho 27) (rho 38) (rho 43) (rho 48) (rho 53) (rho 58)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg8 (rho 6) (rho 12) (rho 18) (rho 27) (rho 38) (rho 43) (rho 48) (rho 53) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart8 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow40 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow41 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow42 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow43 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow44 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg8
  refine ⟨(rho 54), (rho 55), (rho 56), (rho 57), (rho 58), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part9_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart9 rho)
    {k : F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 6) (rho 12) (rho 18) (rho 27) (rho 38) (rho 43) (rho 48) (rho 53) (rho 58) (rho 63)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg9 (rho 6) (rho 12) (rho 18) (rho 27) (rho 38) (rho 43) (rho 48) (rho 53) (rho 58) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart9 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow45 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow46 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow47 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow48 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow49 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg9
  refine ⟨(rho 59), (rho 60), (rho 61), (rho 62), (rho 63), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part10_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart10 rho)
    {k : F → F → F → F → F → F → Prop} (hk : k (rho 43) (rho 48) (rho 53) (rho 58) (rho 63) (rho 68)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg10 (rho 6) (rho 12) (rho 18) (rho 27) (rho 38) (rho 43) (rho 48) (rho 53) (rho 58) (rho 63) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart10 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow50 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow51 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow52 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow53 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow54 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg10
  refine ⟨(rho 64), (rho 65), (rho 66), (rho 67), (rho 68), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part11_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart11 rho)
    {k : F → F → F → F → F → F → F → Prop} (hk : k (rho 43) (rho 48) (rho 53) (rho 58) (rho 63) (rho 68) (rho 73)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg11 (rho 43) (rho 48) (rho 53) (rho 58) (rho 63) (rho 68) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart11 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow55 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow56 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow57 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow58 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow59 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg11
  refine ⟨(rho 69), (rho 70), (rho 71), (rho 72), (rho 73), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part12_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart12 rho)
    {k : F → F → F → F → F → F → F → F → Prop} (hk : k (rho 43) (rho 48) (rho 53) (rho 58) (rho 63) (rho 68) (rho 73) (rho 78)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg12 (rho 43) (rho 48) (rho 53) (rho 58) (rho 63) (rho 68) (rho 73) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart12 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow60 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow61 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow62 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow63 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow64 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg12
  refine ⟨(rho 74), (rho 75), (rho 76), (rho 77), (rho 78), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part13_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart13 rho)
    {k : F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 43) (rho 48) (rho 53) (rho 58) (rho 63) (rho 68) (rho 73) (rho 78) (rho 83)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg13 (rho 43) (rho 48) (rho 53) (rho 58) (rho 63) (rho 68) (rho 73) (rho 78) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart13 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow65 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow66 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow67 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow68 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow69 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg13
  refine ⟨(rho 79), (rho 80), (rho 81), (rho 82), (rho 83), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part14_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart14 rho)
    {k : F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 43) (rho 48) (rho 53) (rho 58) (rho 63) (rho 68) (rho 73) (rho 78) (rho 83) (rho 88)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg14 (rho 43) (rho 48) (rho 53) (rho 58) (rho 63) (rho 68) (rho 73) (rho 78) (rho 83) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart14 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow70 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow71 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow72 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow73 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow74 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg14
  refine ⟨(rho 84), (rho 85), (rho 86), (rho 87), (rho 88), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part15_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart15 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 43) (rho 48) (rho 53) (rho 58) (rho 63) (rho 68) (rho 73) (rho 78) (rho 83) (rho 88) (rho 93)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg15 (rho 43) (rho 48) (rho 53) (rho 58) (rho 63) (rho 68) (rho 73) (rho 78) (rho 83) (rho 88) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart15 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow75 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow76 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow77 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow78 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow79 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg15
  refine ⟨(rho 89), (rho 90), (rho 91), (rho 92), (rho 93), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part16_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart16 rho)
    {k : F → F → F → F → F → F → Prop} (hk : k (rho 73) (rho 78) (rho 83) (rho 88) (rho 93) (rho 98)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg16 (rho 43) (rho 48) (rho 53) (rho 58) (rho 63) (rho 68) (rho 73) (rho 78) (rho 83) (rho 88) (rho 93) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart16 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow80 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow81 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow82 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow83 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow84 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg16
  refine ⟨(rho 94), (rho 95), (rho 96), (rho 97), (rho 98), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part17_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart17 rho)
    {k : F → F → F → F → F → F → F → Prop} (hk : k (rho 73) (rho 78) (rho 83) (rho 88) (rho 93) (rho 98) (rho 103)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg17 (rho 73) (rho 78) (rho 83) (rho 88) (rho 93) (rho 98) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart17 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow85 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow86 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow87 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow88 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow89 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg17
  refine ⟨(rho 99), (rho 100), (rho 101), (rho 102), (rho 103), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part18_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart18 rho)
    {k : F → F → F → F → F → F → F → F → Prop} (hk : k (rho 73) (rho 78) (rho 83) (rho 88) (rho 93) (rho 98) (rho 103) (rho 108)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg18 (rho 73) (rho 78) (rho 83) (rho 88) (rho 93) (rho 98) (rho 103) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart18 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow90 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow91 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow92 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow93 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow94 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg18
  refine ⟨(rho 104), (rho 105), (rho 106), (rho 107), (rho 108), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part19_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart19 rho)
    {k : F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 73) (rho 78) (rho 83) (rho 88) (rho 93) (rho 98) (rho 103) (rho 108) (rho 113)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg19 (rho 73) (rho 78) (rho 83) (rho 88) (rho 93) (rho 98) (rho 103) (rho 108) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart19 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow95 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow96 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow97 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow98 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow99 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg19
  refine ⟨(rho 109), (rho 110), (rho 111), (rho 112), (rho 113), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part20_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart20 rho)
    {k : F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 73) (rho 78) (rho 83) (rho 88) (rho 93) (rho 98) (rho 103) (rho 108) (rho 113) (rho 118)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg20 (rho 73) (rho 78) (rho 83) (rho 88) (rho 93) (rho 98) (rho 103) (rho 108) (rho 113) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart20 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow100 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow101 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow102 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow103 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow104 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg20
  refine ⟨(rho 114), (rho 115), (rho 116), (rho 117), (rho 118), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part21_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart21 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 73) (rho 78) (rho 83) (rho 88) (rho 93) (rho 98) (rho 103) (rho 108) (rho 113) (rho 118) (rho 123)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg21 (rho 73) (rho 78) (rho 83) (rho 88) (rho 93) (rho 98) (rho 103) (rho 108) (rho 113) (rho 118) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart21 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow105 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow106 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow107 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow108 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow109 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg21
  refine ⟨(rho 119), (rho 120), (rho 121), (rho 122), (rho 123), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part22_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart22 rho)
    {k : F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg22 (rho 73) (rho 78) (rho 83) (rho 88) (rho 93) (rho 98) (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart22 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow110 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow111 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow112 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow113 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow114 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg22
  refine ⟨(rho 124), (rho 125), (rho 126), (rho 127), (rho 128), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part23_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart23 rho)
    {k : F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg23 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart23 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow115 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow116 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow117 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow118 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow119 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg23
  refine ⟨(rho 129), (rho 130), (rho 131), (rho 132), (rho 133), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part24_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart24 rho)
    {k : F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg24 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart24 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow120 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow121 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow122 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow123 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow124 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg24
  refine ⟨(rho 134), (rho 135), (rho 136), (rho 137), (rho 138), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part25_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart25 rho)
    {k : F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg25 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart25 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow125 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow126 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow127 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow128 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow129 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg25
  refine ⟨(rho 139), (rho 140), (rho 141), (rho 142), (rho 143), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part26_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart26 rho)
    {k : F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg26 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart26 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow130 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow131 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow132 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow133 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow134 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg26
  refine ⟨(rho 144), (rho 145), (rho 146), (rho 147), (rho 148), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part27_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart27 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg27 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart27 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow135 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow136 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow137 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow138 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow139 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg27
  refine ⟨(rho 149), (rho 150), (rho 151), (rho 152), (rho 153), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part28_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart28 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg28 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart28 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow140 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow141 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow142 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow143 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow144 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg28
  refine ⟨(rho 154), (rho 155), (rho 156), (rho 157), (rho 158), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part29_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart29 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg29 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart29 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow145 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow146 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow147 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow148 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow149 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg29
  refine ⟨(rho 159), (rho 160), (rho 161), (rho 162), (rho 163), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part30_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart30 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg30 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart30 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow150 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow151 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow152 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow153 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow154 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg30
  refine ⟨(rho 164), (rho 165), (rho 166), (rho 167), (rho 168), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part31_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart31 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg31 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart31 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow155 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow156 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow157 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow158 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow159 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg31
  refine ⟨(rho 169), (rho 170), (rho 171), (rho 172), (rho 173), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part32_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart32 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg32 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart32 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow160 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow161 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow162 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow163 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow164 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg32
  refine ⟨(rho 174), (rho 175), (rho 176), (rho 177), (rho 178), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part33_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart33 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg33 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart33 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow165 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow166 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow167 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow168 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow169 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg33
  refine ⟨(rho 179), (rho 180), (rho 181), (rho 182), (rho 183), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part34_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart34 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg34 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart34 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow170 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow171 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow172 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow173 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow174 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg34
  refine ⟨(rho 184), (rho 185), (rho 186), (rho 187), (rho 188), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part35_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart35 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg35 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart35 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow175 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow176 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow177 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow178 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow179 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg35
  refine ⟨(rho 189), (rho 190), (rho 191), (rho 192), (rho 193), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part36_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart36 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg36 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart36 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow180 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow181 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow182 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow183 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow184 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg36
  refine ⟨(rho 194), (rho 195), (rho 196), (rho 197), (rho 198), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part37_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart37 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg37 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart37 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow185 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow186 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow187 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow188 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow189 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg37
  refine ⟨(rho 199), (rho 200), (rho 201), (rho 202), (rho 203), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part38_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart38 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg38 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart38 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow190 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow191 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow192 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow193 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow194 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg38
  refine ⟨(rho 204), (rho 205), (rho 206), (rho 207), (rho 208), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part39_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart39 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg39 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart39 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow195 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow196 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow197 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow198 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow199 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg39
  refine ⟨(rho 209), (rho 210), (rho 211), (rho 212), (rho 213), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part40_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart40 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg40 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart40 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow200 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow201 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow202 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow203 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow204 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg40
  refine ⟨(rho 214), (rho 215), (rho 216), (rho 217), (rho 218), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part41_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart41 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg41 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart41 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow205 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow206 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow207 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow208 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow209 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg41
  refine ⟨(rho 219), (rho 220), (rho 221), (rho 222), (rho 223), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part42_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart42 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg42 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart42 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow210 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow211 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow212 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow213 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow214 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg42
  refine ⟨(rho 224), (rho 225), (rho 226), (rho 227), (rho 228), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part43_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart43 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg43 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart43 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow215 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow216 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow217 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow218 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow219 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg43
  refine ⟨(rho 229), (rho 230), (rho 231), (rho 232), (rho 233), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part44_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart44 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg44 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart44 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow220 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow221 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow222 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow223 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow224 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg44
  refine ⟨(rho 234), (rho 235), (rho 236), (rho 237), (rho 238), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part45_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart45 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) (rho 243)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg45 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart45 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow225 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow226 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow227 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow228 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow229 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg45
  refine ⟨(rho 239), (rho 240), (rho 241), (rho 242), (rho 243), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part46_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart46 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) (rho 243) (rho 248)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg46 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) (rho 243) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart46 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow230 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow231 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow232 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow233 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow234 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg46
  refine ⟨(rho 244), (rho 245), (rho 246), (rho 247), (rho 248), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part47_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart47 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) (rho 243) (rho 248) (rho 253)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg47 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) (rho 243) (rho 248) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart47 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow235 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow236 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow237 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow238 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow239 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg47
  refine ⟨(rho 249), (rho 250), (rho 251), (rho 252), (rho 253), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part48_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart48 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) (rho 243) (rho 248) (rho 253) (rho 258)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg48 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) (rho 243) (rho 248) (rho 253) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart48 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow240 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow241 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow242 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow243 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow244 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg48
  refine ⟨(rho 254), (rho 255), (rho 256), (rho 257), (rho 258), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part49_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart49 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) (rho 243) (rho 248) (rho 253) (rho 258) (rho 263)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg49 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) (rho 243) (rho 248) (rho 253) (rho 258) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart49 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow245 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow246 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow247 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow248 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow249 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg49
  refine ⟨(rho 259), (rho 260), (rho 261), (rho 262), (rho 263), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc0Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc0Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc0Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc0Part1, choiceFreeAddAssoc] using h4

theorem template_part50_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart50 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) (rho 243) (rho 248) (rho 253) (rho 258) (rho 263) (rho 268)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg50 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) (rho 243) (rho 248) (rho 253) (rho 258) (rho 263) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart50 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow250 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow251 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow252 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow253 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow254 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg50
  refine ⟨(rho 264), (rho 265), (rho 266), (rho 267), (rho 268), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc1, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc1Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc1Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc1, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc1Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc1Part1, choiceFreeAddAssoc] using h4

theorem template_part51_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart51 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) (rho 243) (rho 248) (rho 253) (rho 258) (rho 263) (rho 268) (rho 273)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg51 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) (rho 243) (rho 248) (rho 253) (rho 258) (rho 263) (rho 268) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart51 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow255 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow256 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow257 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow258 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow259 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg51
  refine ⟨(rho 269), (rho 270), (rho 271), (rho 272), (rho 273), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc2, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc2Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc2Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc2, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc2Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc2Part1, choiceFreeAddAssoc] using h4

theorem template_part52_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart52 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) (rho 243) (rho 248) (rho 253) (rho 258) (rho 263) (rho 268) (rho 273) (rho 278)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg52 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) (rho 243) (rho 248) (rho 253) (rho 258) (rho 263) (rho 268) (rho 273) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart52 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow260 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow261 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow262 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow263 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow264 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg52
  refine ⟨(rho 274), (rho 275), (rho 276), (rho 277), (rho 278), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc3, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc3Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc3Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc3, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc3Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc3Part1, choiceFreeAddAssoc] using h4

theorem template_part53_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart53 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) (rho 243) (rho 248) (rho 253) (rho 258) (rho 263) (rho 268) (rho 273) (rho 278) (rho 283)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg53 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) (rho 243) (rho 248) (rho 253) (rho 258) (rho 263) (rho 268) (rho 273) (rho 278) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart53 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow265 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow266 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow267 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow268 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow269 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg53
  refine ⟨(rho 279), (rho 280), (rho 281), (rho 282), (rho 283), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc4, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc4Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc4Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc4, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc4Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc4Part1, choiceFreeAddAssoc] using h4

theorem template_part54_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart54 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) (rho 243) (rho 248) (rho 253) (rho 258) (rho 263) (rho 268) (rho 273) (rho 278) (rho 283) (rho 288)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg54 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) (rho 243) (rho 248) (rho 253) (rho 258) (rho 263) (rho 268) (rho 273) (rho 278) (rho 283) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart54 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow270 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow271 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow272 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow273 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow274 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg54
  refine ⟨(rho 284), (rho 285), (rho 286), (rho 287), (rho 288), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc5, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc5Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc5Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc5, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc5Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc5Part1, choiceFreeAddAssoc] using h4

theorem template_part55_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart55 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) (rho 243) (rho 248) (rho 253) (rho 258) (rho 263) (rho 268) (rho 273) (rho 278) (rho 283) (rho 288) (rho 293)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg55 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) (rho 243) (rho 248) (rho 253) (rho 258) (rho 263) (rho 268) (rho 273) (rho 278) (rho 283) (rho 288) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart55 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow275 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow276 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow277 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow278 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow279 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg55
  refine ⟨(rho 289), (rho 290), (rho 291), (rho 292), (rho 293), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc6, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc6Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc6Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc6, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc6Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc6Part1, choiceFreeAddAssoc] using h4

theorem template_part56_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart56 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) (rho 243) (rho 248) (rho 253) (rho 258) (rho 263) (rho 268) (rho 273) (rho 278) (rho 283) (rho 288) (rho 293) (rho 298)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg56 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) (rho 243) (rho 248) (rho 253) (rho 258) (rho 263) (rho 268) (rho 273) (rho 278) (rho 283) (rho 288) (rho 293) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart56 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow280 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow281 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow282 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow283 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow284 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg56
  refine ⟨(rho 294), (rho 295), (rho 296), (rho 297), (rho 298), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc7, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc7Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc7Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc7, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc7Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc7Part1, choiceFreeAddAssoc] using h4

theorem template_part57_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart57 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) (rho 243) (rho 248) (rho 253) (rho 258) (rho 263) (rho 268) (rho 273) (rho 278) (rho 283) (rho 288) (rho 293) (rho 298) (rho 303)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg57 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) (rho 243) (rho 248) (rho 253) (rho 258) (rho 263) (rho 268) (rho 273) (rho 278) (rho 283) (rho 288) (rho 293) (rho 298) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart57 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow285 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow286 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow287 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow288 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow289 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg57
  refine ⟨(rho 299), (rho 300), (rho 301), (rho 302), (rho 303), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc8, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc8Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc8Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc8, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc8Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc8Part1, choiceFreeAddAssoc] using h4

theorem template_part58_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart58 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) (rho 243) (rho 248) (rho 253) (rho 258) (rho 263) (rho 268) (rho 273) (rho 278) (rho 283) (rho 288) (rho 293) (rho 298) (rho 303) (rho 308)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg58 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) (rho 243) (rho 248) (rho 253) (rho 258) (rho 263) (rho 268) (rho 273) (rho 278) (rho 283) (rho 288) (rho 293) (rho 298) (rho 303) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart58 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow290 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow291 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow292 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow293 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow294 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg58
  refine ⟨(rho 304), (rho 305), (rho 306), (rho 307), (rho 308), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc9, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc9Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc9Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc9, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc9Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc9Part1, choiceFreeAddAssoc] using h4

theorem template_part59_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart59 rho)
    {k : F → F → F → F → F → F → Prop} (hk : k (rho 288) (rho 293) (rho 298) (rho 303) (rho 308) (rho 313)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg59 (rho 103) (rho 108) (rho 113) (rho 118) (rho 123) (rho 128) (rho 133) (rho 138) (rho 143) (rho 148) (rho 153) (rho 158) (rho 163) (rho 168) (rho 173) (rho 178) (rho 183) (rho 188) (rho 193) (rho 198) (rho 203) (rho 208) (rho 213) (rho 218) (rho 223) (rho 228) (rho 233) (rho 238) (rho 243) (rho 248) (rho 253) (rho 258) (rho 263) (rho 268) (rho 273) (rho 278) (rho 283) (rho 288) (rho 293) (rho 298) (rho 303) (rho 308) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart59 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow295 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow296 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow297 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow298 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow299 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg59
  refine ⟨(rho 309), (rho 310), (rho 311), (rho 312), (rho 313), ?_, ?_, ?_, ?_, ?_, hk⟩
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc10, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc10Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc10Part1, choiceFreeAddAssoc] using h0
  · exact h1
  · exact h2
  · exact h3
  · have choiceFreeAddAssoc (a b c : F) : a + b + c = a + (b + c) :=
      @add_assoc F providerAddSemigroup a b c
    simpa only [Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc10, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc10Part0, Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationLc10Part1, choiceFreeAddAssoc] using h4

theorem template_part60_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart60 rho)
    {k : F → F → F → F → F → F → F → Prop} (hk : k (rho 288) (rho 293) (rho 298) (rho 303) (rho 308) (rho 313) (rho 318)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg60 (rho 288) (rho 293) (rho 298) (rho 303) (rho 308) (rho 313) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart60 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow300 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow301 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow302 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow303 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow304 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg60
  refine ⟨(rho 314), (rho 315), (rho 316), (rho 317), (rho 318), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part61_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart61 rho)
    {k : F → F → F → F → F → F → F → F → Prop} (hk : k (rho 288) (rho 293) (rho 298) (rho 303) (rho 308) (rho 313) (rho 318) (rho 323)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg61 (rho 288) (rho 293) (rho 298) (rho 303) (rho 308) (rho 313) (rho 318) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart61 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow305 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow306 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow307 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow308 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow309 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg61
  refine ⟨(rho 319), (rho 320), (rho 321), (rho 322), (rho 323), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part62_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart62 rho)
    {k : F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 288) (rho 293) (rho 298) (rho 303) (rho 308) (rho 313) (rho 318) (rho 323) (rho 328)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg62 (rho 288) (rho 293) (rho 298) (rho 303) (rho 308) (rho 313) (rho 318) (rho 323) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart62 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow310 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow311 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow312 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow313 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow314 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg62
  refine ⟨(rho 324), (rho 325), (rho 326), (rho 327), (rho 328), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part63_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart63 rho)
    {k : F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 288) (rho 293) (rho 298) (rho 303) (rho 308) (rho 313) (rho 318) (rho 323) (rho 328) (rho 333)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg63 (rho 288) (rho 293) (rho 298) (rho 303) (rho 308) (rho 313) (rho 318) (rho 323) (rho 328) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart63 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow315 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow316 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow317 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow318 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow319 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg63
  refine ⟨(rho 329), (rho 330), (rho 331), (rho 332), (rho 333), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part64_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart64 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 288) (rho 293) (rho 298) (rho 303) (rho 308) (rho 313) (rho 318) (rho 323) (rho 328) (rho 333) (rho 338)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg64 (rho 288) (rho 293) (rho 298) (rho 303) (rho 308) (rho 313) (rho 318) (rho 323) (rho 328) (rho 333) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart64 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow320 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow321 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow322 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow323 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow324 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg64
  refine ⟨(rho 334), (rho 335), (rho 336), (rho 337), (rho 338), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part65_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart65 rho)
    {k : F → F → F → F → F → F → Prop} (hk : k (rho 318) (rho 323) (rho 328) (rho 333) (rho 338) (rho 343)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg65 (rho 288) (rho 293) (rho 298) (rho 303) (rho 308) (rho 313) (rho 318) (rho 323) (rho 328) (rho 333) (rho 338) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart65 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow325 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow326 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow327 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow328 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow329 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg65
  refine ⟨(rho 339), (rho 340), (rho 341), (rho 342), (rho 343), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part66_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart66 rho)
    {k : F → F → F → F → F → F → F → Prop} (hk : k (rho 318) (rho 323) (rho 328) (rho 333) (rho 338) (rho 343) (rho 348)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg66 (rho 318) (rho 323) (rho 328) (rho 333) (rho 338) (rho 343) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart66 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow330 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow331 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow332 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow333 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow334 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg66
  refine ⟨(rho 344), (rho 345), (rho 346), (rho 347), (rho 348), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part67_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart67 rho)
    {k : F → F → F → F → F → F → F → F → Prop} (hk : k (rho 318) (rho 323) (rho 328) (rho 333) (rho 338) (rho 343) (rho 348) (rho 353)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg67 (rho 318) (rho 323) (rho 328) (rho 333) (rho 338) (rho 343) (rho 348) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart67 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow335 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow336 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow337 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow338 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow339 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg67
  refine ⟨(rho 349), (rho 350), (rho 351), (rho 352), (rho 353), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part68_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart68 rho)
    {k : F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 318) (rho 323) (rho 328) (rho 333) (rho 338) (rho 343) (rho 348) (rho 353) (rho 358)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg68 (rho 318) (rho 323) (rho 328) (rho 333) (rho 338) (rho 343) (rho 348) (rho 353) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart68 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow340 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow341 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow342 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow343 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow344 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg68
  refine ⟨(rho 354), (rho 355), (rho 356), (rho 357), (rho 358), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part69_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart69 rho)
    {k : F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 318) (rho 323) (rho 328) (rho 333) (rho 338) (rho 343) (rho 348) (rho 353) (rho 358) (rho 363)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg69 (rho 318) (rho 323) (rho 328) (rho 333) (rho 338) (rho 343) (rho 348) (rho 353) (rho 358) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart69 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow345 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow346 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow347 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow348 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow349 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg69
  refine ⟨(rho 359), (rho 360), (rho 361), (rho 362), (rho 363), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part70_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart70 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 318) (rho 323) (rho 328) (rho 333) (rho 338) (rho 343) (rho 348) (rho 353) (rho 358) (rho 363) (rho 368)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg70 (rho 318) (rho 323) (rho 328) (rho 333) (rho 338) (rho 343) (rho 348) (rho 353) (rho 358) (rho 363) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart70 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow350 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow351 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow352 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow353 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow354 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg70
  refine ⟨(rho 364), (rho 365), (rho 366), (rho 367), (rho 368), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part71_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart71 rho)
    {k : F → F → F → F → F → F → Prop} (hk : k (rho 348) (rho 353) (rho 358) (rho 363) (rho 368) (rho 373)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg71 (rho 318) (rho 323) (rho 328) (rho 333) (rho 338) (rho 343) (rho 348) (rho 353) (rho 358) (rho 363) (rho 368) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart71 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow355 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow356 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow357 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow358 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow359 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg71
  refine ⟨(rho 369), (rho 370), (rho 371), (rho 372), (rho 373), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part72_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart72 rho)
    {k : F → F → F → F → F → F → F → Prop} (hk : k (rho 348) (rho 353) (rho 358) (rho 363) (rho 368) (rho 373) (rho 378)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg72 (rho 348) (rho 353) (rho 358) (rho 363) (rho 368) (rho 373) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart72 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow360 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow361 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow362 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow363 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow364 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg72
  refine ⟨(rho 374), (rho 375), (rho 376), (rho 377), (rho 378), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part73_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart73 rho)
    {k : F → F → F → F → F → F → F → F → Prop} (hk : k (rho 348) (rho 353) (rho 358) (rho 363) (rho 368) (rho 373) (rho 378) (rho 383)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg73 (rho 348) (rho 353) (rho 358) (rho 363) (rho 368) (rho 373) (rho 378) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart73 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow365 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow366 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow367 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow368 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow369 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg73
  refine ⟨(rho 379), (rho 380), (rho 381), (rho 382), (rho 383), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part74_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart74 rho)
    {k : F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 348) (rho 353) (rho 358) (rho 363) (rho 368) (rho 373) (rho 378) (rho 383) (rho 388)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg74 (rho 348) (rho 353) (rho 358) (rho 363) (rho 368) (rho 373) (rho 378) (rho 383) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart74 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow370 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow371 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow372 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow373 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow374 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg74
  refine ⟨(rho 384), (rho 385), (rho 386), (rho 387), (rho 388), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part75_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart75 rho)
    {k : F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 348) (rho 353) (rho 358) (rho 363) (rho 368) (rho 373) (rho 378) (rho 383) (rho 388) (rho 393)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg75 (rho 348) (rho 353) (rho 358) (rho 363) (rho 368) (rho 373) (rho 378) (rho 383) (rho 388) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart75 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow375 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow376 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow377 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow378 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow379 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg75
  refine ⟨(rho 389), (rho 390), (rho 391), (rho 392), (rho 393), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part76_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart76 rho)
    {k : F → F → F → F → F → F → F → F → F → F → F → Prop} (hk : k (rho 348) (rho 353) (rho 358) (rho 363) (rho 368) (rho 373) (rho 378) (rho 383) (rho 388) (rho 393) (rho 398)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg76 (rho 348) (rho 353) (rho 358) (rho 363) (rho 368) (rho 373) (rho 378) (rho 383) (rho 388) (rho 393) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart76 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow380 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow381 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow382 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow383 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow384 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg76
  refine ⟨(rho 394), (rho 395), (rho 396), (rho 397), (rho 398), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem template_part77_to_extracted (rho : Nat → F)
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart77 rho)
    {k : F → F → F → F → F → F → Prop} (hk : k (rho 378) (rho 383) (rho 388) (rho 393) (rho 398) (rho 403)) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg77 (rho 348) (rho 353) (rho 358) (rho 363) (rho 368) (rho 373) (rho 378) (rho 383) (rho 388) (rho 393) (rho 398) k := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationPart77 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow385 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow386 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow387 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow388 Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relationRow389 at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.seg77
  refine ⟨(rho 399), (rho 400), (rho 401), (rho 402), (rho 403), ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
theorem template_relation_to_poseidon
    (rho : Nat → F) (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relation rho) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.relation (rho 1) (rho 7) (rho 13) (rho 19) (rho 20) (rho 21) (rho 22) (rho 28) (rho 29) (rho 30) (rho 31) (rho 32) (rho 33)
      (fun w378 w383 w388 w393 w398 w403 => w378 = rho 378 ∧ w383 = rho 383 ∧ w388 = rho 388 ∧ w393 = rho 393 ∧ w398 = rho 398 ∧ w403 = rho 403) := by
  unfold Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relation at h
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
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694PoseidonRows390.relation
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
    (h : Shieldd.GnarkFormal.Deployed.Templates.Relations.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db.relation rho) : spec rho := by
  have hExtracted := template_relation_to_poseidon rho h
  rcases Shieldd.GnarkFormal.Deployed.CertifiedGadgetAssetRegistryLeafHash_1d21585b0694Poseidon.relation_sound_permSpec
      (rho 1) (rho 7) (rho 13) (rho 19) (rho 20) (rho 21) (rho 22) (rho 28) (rho 29) (rho 30) (rho 31) (rho 32) (rho 33) _ hExtracted with
    ⟨w378, w383, w388, w393, w398, w403, hk, hperm⟩
  rcases hk with ⟨hw378, hw383, hw388, hw393, hw398, hw403⟩
  unfold spec output
  rw [← hw378, ← hw383, ← hw388, ← hw393, ← hw398, ← hw403]
  exact hperm


end Shieldd.GnarkFormal.Deployed.Templates.Semantics.TGadgetAssetRegistryLeafHash_1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db
