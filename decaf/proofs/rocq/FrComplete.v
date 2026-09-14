From Stdlib Require Import ZArith Lia List.
From Core Require Import Core Carry RustMultiply RustFiatPrimitives RustFieldAdd RustMultiplyWords RustMultiplyRow RustMultiplyRound.
From Slice Require Import Decaf_proof_slice_Fiat NativeMultiplyPrefix.
From FrSlice Require Import Decaf_fr_slice_Fiat.
Require Import FrPrefix FrHelpers FrFirstReduction FrReductionBounds FrRoundDefinition FrRound FrFinalDefinition FrFinal FrChain FrTail.
Require Import FrSuffixDefinition1 FrSuffixDefinition2 FrSuffixDefinition3 FrSuffixDefinition4 FrSuffixDefinition5 FrSuffixDefinition6 FrSuffixDefinition7.
Import ListNotations.
Open Scope Z_scope.
Theorem fr_body_decomposition out a b :
  length a = 8%nat -> length b = 8%nat ->
  Forall U32.canonical a -> Forall U32.canonical b ->
  fr_mul out a b = fr_native_final out (fr_native_accumulate a b).
Proof.
  intros Ha Hb Hca Hcb.
  destruct a as [|d0 a]; [cbn in Ha; discriminate|].
  destruct a as [|d1 a]; [cbn in Ha; discriminate|].
  destruct a as [|d2 a]; [cbn in Ha; discriminate|].
  destruct a as [|d3 a]; [cbn in Ha; discriminate|].
  destruct a as [|d4 a]; [cbn in Ha; discriminate|].
  destruct a as [|d5 a]; [cbn in Ha; discriminate|].
  destruct a as [|d6 a]; [cbn in Ha; discriminate|].
  destruct a as [|d7 a]; [cbn in Ha; discriminate|].
  destruct a; [|cbn in Ha; discriminate].
  pose proof (first_row_words [d0;d1;d2;d3;d4;d5;d6;d7] b eq_refl Hb Hca Hcb) as Hpwords.
  repeat match goal with H : Forall _ (_::_) |- _ => inversion H; subst; clear H end.
  set (product := native_first_row [d0;d1;d2;d3;d4;d5;d6;d7] b).
  fold product in Hpwords.
  pose proof (first_row_length [d0;d1;d2;d3;d4;d5;d6;d7] b) as Hplen. fold product in Hplen.
  set (s0 := fr_redc_words product).
  pose proof (fr_first_redc_length product Hplen) as Hl0. fold s0 in Hl0.
  pose proof (fr_first_redc_words product Hplen Hpwords) as Hc0. fold s0 in Hc0.
  set (s1 := fr_native_round d1 b s0).
  destruct (fr_round_shape d1 b s0 ltac:(assumption) Hb Hl0 Hcb Hc0) as [Hl1 Hc1].
  fold s1 in Hl1, Hc1.
  set (s2 := fr_native_round d2 b s1).
  destruct (fr_round_shape d2 b s1 ltac:(assumption) Hb Hl1 Hcb Hc1) as [Hl2 Hc2].
  fold s2 in Hl2, Hc2.
  set (s3 := fr_native_round d3 b s2).
  destruct (fr_round_shape d3 b s2 ltac:(assumption) Hb Hl2 Hcb Hc2) as [Hl3 Hc3].
  fold s3 in Hl3, Hc3.
  set (s4 := fr_native_round d4 b s3).
  destruct (fr_round_shape d4 b s3 ltac:(assumption) Hb Hl3 Hcb Hc3) as [Hl4 Hc4].
  fold s4 in Hl4, Hc4.
  set (s5 := fr_native_round d5 b s4).
  destruct (fr_round_shape d5 b s4 ltac:(assumption) Hb Hl4 Hcb Hc4) as [Hl5 Hc5].
  fold s5 in Hl5, Hc5.
  set (s6 := fr_native_round d6 b s5).
  destruct (fr_round_shape d6 b s5 ltac:(assumption) Hb Hl5 Hcb Hc5) as [Hl6 Hc6].
  fold s6 in Hl6, Hc6.
  set (s7 := fr_native_round d7 b s6).
  destruct (fr_round_shape d7 b s6 ltac:(assumption) Hb Hl6 Hcb Hc6) as [Hl7 Hc7].
  fold s7 in Hl7, Hc7.
  rewrite fr_first_row_decomposition, fr_first_row_same, fr_first_redc_decomposition.
  fold product.
  rewrite fr_initial_tail_decomposition by (apply fr_redc_state_length; assumption).
  change (fr_native_suffix1 out [d0;d1;d2;d3;d4;d5;d6;d7] b s0 = fr_native_final out (fr_native_accumulate [d0;d1;d2;d3;d4;d5;d6;d7] b)).
  rewrite fr_round1_decomposition by exact Hl0.
  change (fr_native_suffix2 out [d0;d1;d2;d3;d4;d5;d6;d7] b s1 = fr_native_final out (fr_native_accumulate [d0;d1;d2;d3;d4;d5;d6;d7] b)).
  rewrite fr_round2_decomposition by exact Hl1.
  change (fr_native_suffix3 out [d0;d1;d2;d3;d4;d5;d6;d7] b s2 = fr_native_final out (fr_native_accumulate [d0;d1;d2;d3;d4;d5;d6;d7] b)).
  rewrite fr_round3_decomposition by exact Hl2.
  change (fr_native_suffix4 out [d0;d1;d2;d3;d4;d5;d6;d7] b s3 = fr_native_final out (fr_native_accumulate [d0;d1;d2;d3;d4;d5;d6;d7] b)).
  rewrite fr_round4_decomposition by exact Hl3.
  change (fr_native_suffix5 out [d0;d1;d2;d3;d4;d5;d6;d7] b s4 = fr_native_final out (fr_native_accumulate [d0;d1;d2;d3;d4;d5;d6;d7] b)).
  rewrite fr_round5_decomposition by exact Hl4.
  change (fr_native_suffix6 out [d0;d1;d2;d3;d4;d5;d6;d7] b s5 = fr_native_final out (fr_native_accumulate [d0;d1;d2;d3;d4;d5;d6;d7] b)).
  rewrite fr_round6_decomposition by exact Hl5.
  change (fr_native_suffix7 out [d0;d1;d2;d3;d4;d5;d6;d7] b s6 = fr_native_final out (fr_native_accumulate [d0;d1;d2;d3;d4;d5;d6;d7] b)).
  rewrite fr_round7_decomposition by exact Hl6.
  change (fr_native_final out s7 = fr_native_final out (fr_native_accumulate [d0;d1;d2;d3;d4;d5;d6;d7] b)).
  unfold fr_native_accumulate. cbn [tl]. fold product. fold s0.
  cbn [fr_native_rounds]. reflexivity.
Qed.
Print Assumptions fr_body_decomposition.
Theorem fr_multiplication_correct out a b :
  length out = 8%nat -> length a = 8%nat -> length b = 8%nat ->
  Forall U32.canonical a -> Forall U32.canonical b ->
  0 <= limbs_value b < fr_modulus ->
  let result := fr_mul out a b in
  length result = 8%nat /\ Forall U32.canonical result /\
  0 <= limbs_value result < fr_modulus /\
  exists k, 4294967296^8 * limbs_value result =
    limbs_value a * limbs_value b + fr_modulus*k.
Proof.
  intros Ho Ha Hb Hca Hcb Hbv.
  rewrite fr_body_decomposition by assumption.
  destruct (fr_accumulator_correct a b Ha Hb Hca Hcb Hbv)
    as [Htlen [Htcan [Htbound [k Htvalue]]]].
  destruct (fr_final_correct out (fr_native_accumulate a b) Ho Htlen Htcan Htbound)
    as [Hlen [Hcan Hvalue]].
  split; [exact Hlen|]. split; [exact Hcan|]. rewrite Hvalue.
  split; [apply Z.mod_pos_bound; unfold fr_modulus; lia|].
  exists (k - 4294967296^8 * (limbs_value (fr_native_accumulate a b) / fr_modulus)).
  pose proof (Z.div_mod (limbs_value (fr_native_accumulate a b)) fr_modulus ltac:(unfold fr_modulus; lia)) as Hdiv.
  clear - Htvalue Hdiv.
  unfold fr_modulus in *. nia.
Qed.


Theorem fr_output_state_independent out other a b :
  length out = 8%nat -> length other = 8%nat ->
  length a = 8%nat -> length b = 8%nat ->
  Forall U32.canonical a -> Forall U32.canonical b ->
  0 <= limbs_value b < fr_modulus ->
  fr_mul out a b = fr_mul other a b.
Proof.
  intros Ho Hother Ha Hb Hca Hcb Hbv.
  rewrite !fr_body_decomposition by assumption.
  apply fr_final_state_independent; try assumption.
  exact (proj1 (fr_accumulator_correct a b Ha Hb Hca Hcb Hbv)).
Qed.
Print Assumptions fr_multiplication_correct.
Print Assumptions fr_output_state_independent.
