import ShielddGnarkFormal.ChoiceFreeZModCast
import ShielddGnarkFormal.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0Poseidon.SegSound

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

theorem range0_sound (w1 : F) (w2 : F) (w8 : F) (w14 : F) (k : F → F → F → F → Prop)
    (h : Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg0 w1 w2 w8 w14 (fun w8 w14 w7 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg1 w7 w8 w14 (fun w7 w14 w13 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg2 w7 w13 w14 (fun w7 w13 w19 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg3 w7 w13 w19 (fun w7 w13 w19 w24 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg4 w7 w13 w19 w24 (fun w7 w13 w19 w24 w29 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg5 w7 w13 w19 w24 w29 (fun w7 w13 w19 w24 w29 w34 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg6 w7 w13 w19 w24 w29 w34 (fun w24 w29 w34 w39 =>
      k w24 w29 w34 w39)))))))) :
    ∃ w24 w29 w34 w39 : F, spec1 ((-1 : F) * w1 + w2) (w8) (w14) = st1 w24 w29 w34 w39 ∧ k w24 w29 w34 w39 := by
  have h0 := seg0_sound w1 w2 w8 w14 _ h
  rcases h0 with ⟨w7, hw7, h⟩
  have h1 := seg1_sound w7 w8 w14 _ h
  rcases h1 with ⟨w13, hw13, h⟩
  have h2 := seg2_sound w7 w13 w14 _ h
  rcases h2 with ⟨w19, hw19, h⟩
  have hSpec0 := spec0_eq ((-1 : F) * w1 + w2) (w8) (w14) w7 w13 w19 hw7 hw13 hw19
  have h3 := seg3_sound w7 w13 w19 _ h
  rcases h3 with ⟨w24, hw24, h⟩
  have h4 := seg4_sound w7 w13 w19 w24 _ h
  rcases h4 with ⟨w29, hw29, h⟩
  have h5 := seg5_sound w7 w13 w19 w24 w29 _ h
  rcases h5 with ⟨w34, hw34, h⟩
  have h6 := seg6_sound w7 w13 w19 w24 w29 w34 _ h
  rcases h6 with ⟨w39, hw39, h⟩
  have hSpec1 := spec1_step ((-1 : F) * w1 + w2) (w8) (w14) w7 w13 w19 w24 w29 w34 w39 hSpec0 hw24 hw29 hw34 hw39
  exact ⟨w24, w29, w34, w39, hSpec1, h⟩

theorem range1_sound (w1 : F) (w2 : F) (w8 : F) (w14 : F) (w24 : F) (w29 : F) (w34 : F) (w39 : F) (k : F → F → F → F → Prop)
    (hSpec1 : spec1 ((-1 : F) * w1 + w2) (w8) (w14) = st1 w24 w29 w34 w39)
    (h : Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg7 w24 w29 w34 w39 (fun w24 w29 w34 w39 w44 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg8 w24 w29 w34 w39 w44 (fun w24 w29 w34 w39 w44 w49 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg9 w24 w29 w34 w39 w44 w49 (fun w24 w29 w34 w39 w44 w49 w54 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg10 w24 w29 w34 w39 w44 w49 w54 (fun w44 w49 w54 w59 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg11 w44 w49 w54 w59 (fun w44 w49 w54 w59 w64 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg12 w44 w49 w54 w59 w64 (fun w44 w49 w54 w59 w64 w69 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg13 w44 w49 w54 w59 w64 w69 (fun w44 w49 w54 w59 w64 w69 w74 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg14 w44 w49 w54 w59 w64 w69 w74 (fun w64 w69 w74 w79 =>
      k w64 w69 w74 w79))))))))) :
    ∃ w64 w69 w74 w79 : F, spec3 ((-1 : F) * w1 + w2) (w8) (w14) = st3 w64 w69 w74 w79 ∧ k w64 w69 w74 w79 := by
  have h7 := seg7_sound w24 w29 w34 w39 _ h
  rcases h7 with ⟨w44, hw44, h⟩
  have h8 := seg8_sound w24 w29 w34 w39 w44 _ h
  rcases h8 with ⟨w49, hw49, h⟩
  have h9 := seg9_sound w24 w29 w34 w39 w44 w49 _ h
  rcases h9 with ⟨w54, hw54, h⟩
  have h10 := seg10_sound w24 w29 w34 w39 w44 w49 w54 _ h
  rcases h10 with ⟨w59, hw59, h⟩
  have hSpec2 := spec2_step ((-1 : F) * w1 + w2) (w8) (w14) w24 w29 w34 w39 w44 w49 w54 w59 hSpec1 hw44 hw49 hw54 hw59
  have h11 := seg11_sound w44 w49 w54 w59 _ h
  rcases h11 with ⟨w64, hw64, h⟩
  have h12 := seg12_sound w44 w49 w54 w59 w64 _ h
  rcases h12 with ⟨w69, hw69, h⟩
  have h13 := seg13_sound w44 w49 w54 w59 w64 w69 _ h
  rcases h13 with ⟨w74, hw74, h⟩
  have h14 := seg14_sound w44 w49 w54 w59 w64 w69 w74 _ h
  rcases h14 with ⟨w79, hw79, h⟩
  have hSpec3 := spec3_step ((-1 : F) * w1 + w2) (w8) (w14) w44 w49 w54 w59 w64 w69 w74 w79 hSpec2 hw64 hw69 hw74 hw79
  exact ⟨w64, w69, w74, w79, hSpec3, h⟩

theorem range2_sound (w1 : F) (w2 : F) (w8 : F) (w14 : F) (w64 : F) (w69 : F) (w74 : F) (w79 : F) (k : F → F → F → F → F → F → F → F → F → F → F → F → Prop)
    (hSpec3 : spec3 ((-1 : F) * w1 + w2) (w8) (w14) = st3 w64 w69 w74 w79)
    (h : Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg15 w64 w69 w74 w79 (fun w64 w69 w74 w79 w84 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg16 w64 w69 w74 w79 w84 (fun w64 w69 w74 w79 w84 w89 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg17 w64 w69 w74 w79 w84 w89 (fun w64 w69 w74 w79 w84 w89 w94 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg18 w64 w69 w74 w79 w84 w89 w94 (fun w64 w69 w74 w79 w84 w89 w94 w99 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg19 w64 w69 w74 w79 w84 w89 w94 w99 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg20 w64 w69 w74 w79 w84 w89 w94 w99 w104 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg21 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg22 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 =>
      k w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119))))))))) :
    ∃ w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 : F, spec11 ((-1 : F) * w1 + w2) (w8) (w14) = st11 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 ∧ k w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 := by
  have h15 := seg15_sound w64 w69 w74 w79 _ h
  rcases h15 with ⟨w84, hw84, h⟩
  have hSpec4 := spec4_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 hSpec3 hw84
  have h16 := seg16_sound w64 w69 w74 w79 w84 _ h
  rcases h16 with ⟨w89, hw89, h⟩
  have hSpec5 := spec5_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 hSpec4 hw89
  have h17 := seg17_sound w64 w69 w74 w79 w84 w89 _ h
  rcases h17 with ⟨w94, hw94, h⟩
  have hSpec6 := spec6_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 hSpec5 hw94
  have h18 := seg18_sound w64 w69 w74 w79 w84 w89 w94 _ h
  rcases h18 with ⟨w99, hw99, h⟩
  have hSpec7 := spec7_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 hSpec6 hw99
  have h19 := seg19_sound w64 w69 w74 w79 w84 w89 w94 w99 _ h
  rcases h19 with ⟨w104, hw104, h⟩
  have hSpec8 := spec8_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 w104 hSpec7 hw104
  have h20 := seg20_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 _ h
  rcases h20 with ⟨w109, hw109, h⟩
  have hSpec9 := spec9_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 hSpec8 hw109
  have h21 := seg21_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 _ h
  rcases h21 with ⟨w114, hw114, h⟩
  have hSpec10 := spec10_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 hSpec9 hw114
  have h22 := seg22_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 _ h
  rcases h22 with ⟨w119, hw119, h⟩
  have hSpec11 := spec11_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 hSpec10 hw119
  exact ⟨w64, w69, w74, w79, w84, w89, w94, w99, w104, w109, w114, w119, hSpec11, h⟩

theorem range3_sound (w1 : F) (w2 : F) (w8 : F) (w14 : F) (w64 : F) (w69 : F) (w74 : F) (w79 : F) (w84 : F) (w89 : F) (w94 : F) (w99 : F) (w104 : F) (w109 : F) (w114 : F) (w119 : F) (k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop)
    (hSpec11 : spec11 ((-1 : F) * w1 + w2) (w8) (w14) = st11 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119)
    (h : Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg23 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg24 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg25 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg26 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg27 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg28 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg29 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg30 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 =>
      k w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159))))))))) :
    ∃ w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 : F, spec19 ((-1 : F) * w1 + w2) (w8) (w14) = st19 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 ∧ k w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 := by
  have h23 := seg23_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 _ h
  rcases h23 with ⟨w124, hw124, h⟩
  have hSpec12 := spec12_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 hSpec11 hw124
  have h24 := seg24_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 _ h
  rcases h24 with ⟨w129, hw129, h⟩
  have hSpec13 := spec13_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 hSpec12 hw129
  have h25 := seg25_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 _ h
  rcases h25 with ⟨w134, hw134, h⟩
  have hSpec14 := spec14_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 hSpec13 hw134
  have h26 := seg26_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 _ h
  rcases h26 with ⟨w139, hw139, h⟩
  have hSpec15 := spec15_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 hSpec14 hw139
  have h27 := seg27_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 _ h
  rcases h27 with ⟨w144, hw144, h⟩
  have hSpec16 := spec16_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 hSpec15 hw144
  have h28 := seg28_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 _ h
  rcases h28 with ⟨w149, hw149, h⟩
  have hSpec17 := spec17_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 hSpec16 hw149
  have h29 := seg29_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 _ h
  rcases h29 with ⟨w154, hw154, h⟩
  have hSpec18 := spec18_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 hSpec17 hw154
  have h30 := seg30_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 _ h
  rcases h30 with ⟨w159, hw159, h⟩
  have hSpec19 := spec19_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 hSpec18 hw159
  exact ⟨w64, w69, w74, w79, w84, w89, w94, w99, w104, w109, w114, w119, w124, w129, w134, w139, w144, w149, w154, w159, hSpec19, h⟩

theorem range4_sound (w1 : F) (w2 : F) (w8 : F) (w14 : F) (w64 : F) (w69 : F) (w74 : F) (w79 : F) (w84 : F) (w89 : F) (w94 : F) (w99 : F) (w104 : F) (w109 : F) (w114 : F) (w119 : F) (w124 : F) (w129 : F) (w134 : F) (w139 : F) (w144 : F) (w149 : F) (w154 : F) (w159 : F) (k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop)
    (hSpec19 : spec19 ((-1 : F) * w1 + w2) (w8) (w14) = st19 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159)
    (h : Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg31 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg32 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg33 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg34 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg35 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg36 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg37 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg38 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 =>
      k w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199))))))))) :
    ∃ w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 : F, spec27 ((-1 : F) * w1 + w2) (w8) (w14) = st27 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 ∧ k w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 := by
  have h31 := seg31_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 _ h
  rcases h31 with ⟨w164, hw164, h⟩
  have hSpec20 := spec20_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 hSpec19 hw164
  have h32 := seg32_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 _ h
  rcases h32 with ⟨w169, hw169, h⟩
  have hSpec21 := spec21_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 hSpec20 hw169
  have h33 := seg33_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 _ h
  rcases h33 with ⟨w174, hw174, h⟩
  have hSpec22 := spec22_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 hSpec21 hw174
  have h34 := seg34_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 _ h
  rcases h34 with ⟨w179, hw179, h⟩
  have hSpec23 := spec23_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 hSpec22 hw179
  have h35 := seg35_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 _ h
  rcases h35 with ⟨w184, hw184, h⟩
  have hSpec24 := spec24_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 hSpec23 hw184
  have h36 := seg36_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 _ h
  rcases h36 with ⟨w189, hw189, h⟩
  have hSpec25 := spec25_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 hSpec24 hw189
  have h37 := seg37_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 _ h
  rcases h37 with ⟨w194, hw194, h⟩
  have hSpec26 := spec26_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 hSpec25 hw194
  have h38 := seg38_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 _ h
  rcases h38 with ⟨w199, hw199, h⟩
  have hSpec27 := spec27_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 hSpec26 hw199
  exact ⟨w64, w69, w74, w79, w84, w89, w94, w99, w104, w109, w114, w119, w124, w129, w134, w139, w144, w149, w154, w159, w164, w169, w174, w179, w184, w189, w194, w199, hSpec27, h⟩

theorem range5_sound (w1 : F) (w2 : F) (w8 : F) (w14 : F) (w64 : F) (w69 : F) (w74 : F) (w79 : F) (w84 : F) (w89 : F) (w94 : F) (w99 : F) (w104 : F) (w109 : F) (w114 : F) (w119 : F) (w124 : F) (w129 : F) (w134 : F) (w139 : F) (w144 : F) (w149 : F) (w154 : F) (w159 : F) (w164 : F) (w169 : F) (w174 : F) (w179 : F) (w184 : F) (w189 : F) (w194 : F) (w199 : F) (k : F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → F → Prop)
    (hSpec27 : spec27 ((-1 : F) * w1 + w2) (w8) (w14) = st27 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199)
    (h : Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg39 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg40 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg41 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg42 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg43 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 w224 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg44 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 w224 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 w224 w229 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg45 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 w224 w229 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 w224 w229 w234 =>
      k w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 w224 w229 w234)))))))) :
    ∃ w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 w224 w229 w234 : F, spec34 ((-1 : F) * w1 + w2) (w8) (w14) = st34 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 w224 w229 w234 ∧ k w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 w224 w229 w234 := by
  have h39 := seg39_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 _ h
  rcases h39 with ⟨w204, hw204, h⟩
  have hSpec28 := spec28_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 hSpec27 hw204
  have h40 := seg40_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 _ h
  rcases h40 with ⟨w209, hw209, h⟩
  have hSpec29 := spec29_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 hSpec28 hw209
  have h41 := seg41_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 _ h
  rcases h41 with ⟨w214, hw214, h⟩
  have hSpec30 := spec30_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 hSpec29 hw214
  have h42 := seg42_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 _ h
  rcases h42 with ⟨w219, hw219, h⟩
  have hSpec31 := spec31_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 hSpec30 hw219
  have h43 := seg43_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 _ h
  rcases h43 with ⟨w224, hw224, h⟩
  have hSpec32 := spec32_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 w224 hSpec31 hw224
  have h44 := seg44_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 w224 _ h
  rcases h44 with ⟨w229, hw229, h⟩
  have hSpec33 := spec33_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 w224 w229 hSpec32 hw229
  have h45 := seg45_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 w224 w229 _ h
  rcases h45 with ⟨w234, hw234, h⟩
  have hSpec34 := spec34_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 w224 w229 w234 hSpec33 hw234
  exact ⟨w64, w69, w74, w79, w84, w89, w94, w99, w104, w109, w114, w119, w124, w129, w134, w139, w144, w149, w154, w159, w164, w169, w174, w179, w184, w189, w194, w199, w204, w209, w214, w219, w224, w229, w234, hSpec34, h⟩

theorem range6_sound (w1 : F) (w2 : F) (w8 : F) (w14 : F) (w64 : F) (w69 : F) (w74 : F) (w79 : F) (w84 : F) (w89 : F) (w94 : F) (w99 : F) (w104 : F) (w109 : F) (w114 : F) (w119 : F) (w124 : F) (w129 : F) (w134 : F) (w139 : F) (w144 : F) (w149 : F) (w154 : F) (w159 : F) (w164 : F) (w169 : F) (w174 : F) (w179 : F) (w184 : F) (w189 : F) (w194 : F) (w199 : F) (w204 : F) (w209 : F) (w214 : F) (w219 : F) (w224 : F) (w229 : F) (w234 : F) (k : F → F → F → F → Prop)
    (hSpec34 : spec34 ((-1 : F) * w1 + w2) (w8) (w14) = st34 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 w224 w229 w234)
    (h : Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg46 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 w224 w229 w234 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 w224 w229 w234 w239 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg47 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 w224 w229 w234 w239 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 w224 w229 w234 w239 w244 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg48 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 w224 w229 w234 w239 w244 (fun w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 w224 w229 w234 w239 w244 w249 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg49 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 w224 w229 w234 w239 w244 w249 (fun w239 w244 w249 w254 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg50 w239 w244 w249 w254 (fun w239 w244 w249 w254 w259 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg51 w239 w244 w249 w254 w259 (fun w239 w244 w249 w254 w259 w264 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg52 w239 w244 w249 w254 w259 w264 (fun w239 w244 w249 w254 w259 w264 w269 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg53 w239 w244 w249 w254 w259 w264 w269 (fun w259 w264 w269 w274 =>
      k w259 w264 w269 w274))))))))) :
    ∃ w259 w264 w269 w274 : F, spec36 ((-1 : F) * w1 + w2) (w8) (w14) = st36 w259 w264 w269 w274 ∧ k w259 w264 w269 w274 := by
  have h46 := seg46_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 w224 w229 w234 _ h
  rcases h46 with ⟨w239, hw239, h⟩
  have h47 := seg47_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 w224 w229 w234 w239 _ h
  rcases h47 with ⟨w244, hw244, h⟩
  have h48 := seg48_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 w224 w229 w234 w239 w244 _ h
  rcases h48 with ⟨w249, hw249, h⟩
  have h49 := seg49_sound w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 w224 w229 w234 w239 w244 w249 _ h
  rcases h49 with ⟨w254, hw254, h⟩
  have hSpec35 := spec35_step ((-1 : F) * w1 + w2) (w8) (w14) w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 w224 w229 w234 w239 w244 w249 w254 hSpec34 hw239 hw244 hw249 hw254
  have h50 := seg50_sound w239 w244 w249 w254 _ h
  rcases h50 with ⟨w259, hw259, h⟩
  have h51 := seg51_sound w239 w244 w249 w254 w259 _ h
  rcases h51 with ⟨w264, hw264, h⟩
  have h52 := seg52_sound w239 w244 w249 w254 w259 w264 _ h
  rcases h52 with ⟨w269, hw269, h⟩
  have h53 := seg53_sound w239 w244 w249 w254 w259 w264 w269 _ h
  rcases h53 with ⟨w274, hw274, h⟩
  have hSpec36 := spec36_step ((-1 : F) * w1 + w2) (w8) (w14) w239 w244 w249 w254 w259 w264 w269 w274 hSpec35 hw259 hw264 hw269 hw274
  exact ⟨w259, w264, w269, w274, hSpec36, h⟩

theorem range7_sound (w1 : F) (w2 : F) (w8 : F) (w14 : F) (w259 : F) (w264 : F) (w269 : F) (w274 : F) (k : F → F → F → F → Prop)
    (hSpec36 : spec36 ((-1 : F) * w1 + w2) (w8) (w14) = st36 w259 w264 w269 w274)
    (h : Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg54 w259 w264 w269 w274 (fun w259 w264 w269 w274 w279 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg55 w259 w264 w269 w274 w279 (fun w259 w264 w269 w274 w279 w284 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg56 w259 w264 w269 w274 w279 w284 (fun w259 w264 w269 w274 w279 w284 w289 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg57 w259 w264 w269 w274 w279 w284 w289 (fun w279 w284 w289 w294 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg58 w279 w284 w289 w294 (fun w279 w284 w289 w294 w299 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg59 w279 w284 w289 w294 w299 (fun w279 w284 w289 w294 w299 w304 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg60 w279 w284 w289 w294 w299 w304 (fun w279 w284 w289 w294 w299 w304 w309 =>
      Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.seg61 w279 w284 w289 w294 w299 w304 w309 (fun w299 w304 w309 w314 =>
      k w299 w304 w309 w314))))))))) :
    ∃ w299 w304 w309 w314 : F, spec38 ((-1 : F) * w1 + w2) (w8) (w14) = st38 w299 w304 w309 w314 ∧ k w299 w304 w309 w314 := by
  have h54 := seg54_sound w259 w264 w269 w274 _ h
  rcases h54 with ⟨w279, hw279, h⟩
  have h55 := seg55_sound w259 w264 w269 w274 w279 _ h
  rcases h55 with ⟨w284, hw284, h⟩
  have h56 := seg56_sound w259 w264 w269 w274 w279 w284 _ h
  rcases h56 with ⟨w289, hw289, h⟩
  have h57 := seg57_sound w259 w264 w269 w274 w279 w284 w289 _ h
  rcases h57 with ⟨w294, hw294, h⟩
  have hSpec37 := spec37_step ((-1 : F) * w1 + w2) (w8) (w14) w259 w264 w269 w274 w279 w284 w289 w294 hSpec36 hw279 hw284 hw289 hw294
  have h58 := seg58_sound w279 w284 w289 w294 _ h
  rcases h58 with ⟨w299, hw299, h⟩
  have h59 := seg59_sound w279 w284 w289 w294 w299 _ h
  rcases h59 with ⟨w304, hw304, h⟩
  have h60 := seg60_sound w279 w284 w289 w294 w299 w304 _ h
  rcases h60 with ⟨w309, hw309, h⟩
  have h61 := seg61_sound w279 w284 w289 w294 w299 w304 w309 _ h
  rcases h61 with ⟨w314, hw314, h⟩
  have hSpec38 := spec38_step ((-1 : F) * w1 + w2) (w8) (w14) w279 w284 w289 w294 w299 w304 w309 w314 hSpec37 hw299 hw304 hw309 hw314
  exact ⟨w299, w304, w309, w314, hSpec38, h⟩

theorem relation_sound_permSpec (w1 : F) (w2 : F) (w8 : F) (w14 : F) (k : F → F → F → F → Prop) :
    Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.relation w1 w2 w8 w14 k →
      ∃ w299 w304 w309 w314 : F, k w299 w304 w309 w314 ∧
        s38_1 w299 w304 w309 w314 = permSpec3 domainLit ((-1 : F) * w1 + w2) (w8) (w14) := by
  unfold Shieldd.GnarkFormal.Extracted.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0PoseidonRows310.relation
  intro h
  have r0 := range0_sound w1 w2 w8 w14 _ h
  rcases r0 with ⟨w24, w29, w34, w39, hSpec1, h⟩
  have r1 := range1_sound w1 w2 w8 w14 w24 w29 w34 w39 _ hSpec1 h
  rcases r1 with ⟨w64, w69, w74, w79, hSpec3, h⟩
  have r2 := range2_sound w1 w2 w8 w14 w64 w69 w74 w79 _ hSpec3 h
  rcases r2 with ⟨w64, w69, w74, w79, w84, w89, w94, w99, w104, w109, w114, w119, hSpec11, h⟩
  have r3 := range3_sound w1 w2 w8 w14 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 _ hSpec11 h
  rcases r3 with ⟨w64, w69, w74, w79, w84, w89, w94, w99, w104, w109, w114, w119, w124, w129, w134, w139, w144, w149, w154, w159, hSpec19, h⟩
  have r4 := range4_sound w1 w2 w8 w14 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 _ hSpec19 h
  rcases r4 with ⟨w64, w69, w74, w79, w84, w89, w94, w99, w104, w109, w114, w119, w124, w129, w134, w139, w144, w149, w154, w159, w164, w169, w174, w179, w184, w189, w194, w199, hSpec27, h⟩
  have r5 := range5_sound w1 w2 w8 w14 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 _ hSpec27 h
  rcases r5 with ⟨w64, w69, w74, w79, w84, w89, w94, w99, w104, w109, w114, w119, w124, w129, w134, w139, w144, w149, w154, w159, w164, w169, w174, w179, w184, w189, w194, w199, w204, w209, w214, w219, w224, w229, w234, hSpec34, h⟩
  have r6 := range6_sound w1 w2 w8 w14 w64 w69 w74 w79 w84 w89 w94 w99 w104 w109 w114 w119 w124 w129 w134 w139 w144 w149 w154 w159 w164 w169 w174 w179 w184 w189 w194 w199 w204 w209 w214 w219 w224 w229 w234 _ hSpec34 h
  rcases r6 with ⟨w259, w264, w269, w274, hSpec36, h⟩
  have r7 := range7_sound w1 w2 w8 w14 w259 w264 w269 w274 _ hSpec36 h
  rcases r7 with ⟨w299, w304, w309, w314, hSpec38, h⟩
  refine ⟨w299, w304, w309, w314, h, ?_⟩
  rw [← spec38_eq_permSpec ((-1 : F) * w1 + w2) (w8) (w14)]
  rw [hSpec38]
  simp [st38]

#print axioms relation_sound_permSpec

end Shieldd.GnarkFormal.Deployed.CertifiedGadgetAssetRegistryParamsHash_1963568e22e0Poseidon
