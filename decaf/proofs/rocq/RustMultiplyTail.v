From Stdlib Require Import ZArith Lia List.
From Core Require Import Core Carry RustMultiply RustFiatPrimitives RustFieldAdd RustMultiplyWords RustMultiplyRow RustFirstReduction RustMultiplyRound.
From Slice Require Import Decaf_proof_slice_Fiat NativeMultiplyPrefix.
Import ListNotations.
Open Scope Z_scope.
From Slice Require Export NativeSuffixDefinition1 NativeSuffixDefinition2 NativeSuffixDefinition3 NativeSuffixDefinition4 NativeSuffixDefinition5 NativeSuffixDefinition6 NativeSuffixDefinition7 NativeSuffixDefinition8.
Theorem round1_decomposition out a b acc : length acc = 9%nat ->
  native_suffix1 out a b acc = native_suffix2 out a b (native_round (f_index a (1:t_usize)) b acc).
Proof.
  intros Hlen. array9 acc Hlen.
  unfold native_suffix1, native_suffix2, native_round.
  do 8 plain_product. do 7 plain_carry. do 9 plain_carry.
  do 8 plain_product. do 15 plain_carry.
  exact_tails.
Qed.
Print Assumptions round1_decomposition.
Theorem round2_decomposition out a b acc : length acc = 9%nat ->
  native_suffix2 out a b acc = native_suffix3 out a b (native_round (f_index a (2:t_usize)) b acc).
Proof.
  intros Hlen. array9 acc Hlen.
  unfold native_suffix2, native_suffix3, native_round.
  do 8 plain_product. do 7 plain_carry. do 9 plain_carry.
  do 8 plain_product. do 15 plain_carry.
  exact_tails.
Qed.
Print Assumptions round2_decomposition.
Theorem round3_decomposition out a b acc : length acc = 9%nat ->
  native_suffix3 out a b acc = native_suffix4 out a b (native_round (f_index a (3:t_usize)) b acc).
Proof.
  intros Hlen. array9 acc Hlen.
  unfold native_suffix3, native_suffix4, native_round.
  do 8 plain_product. do 7 plain_carry. do 9 plain_carry.
  do 8 plain_product. do 15 plain_carry.
  exact_tails.
Qed.
Print Assumptions round3_decomposition.
Theorem round4_decomposition out a b acc : length acc = 9%nat ->
  native_suffix4 out a b acc = native_suffix5 out a b (native_round (f_index a (4:t_usize)) b acc).
Proof.
  intros Hlen. array9 acc Hlen.
  unfold native_suffix4, native_suffix5, native_round.
  do 8 plain_product. do 7 plain_carry. do 9 plain_carry.
  do 8 plain_product. do 15 plain_carry.
  exact_tails.
Qed.
Print Assumptions round4_decomposition.
Theorem round5_decomposition out a b acc : length acc = 9%nat ->
  native_suffix5 out a b acc = native_suffix6 out a b (native_round (f_index a (5:t_usize)) b acc).
Proof.
  intros Hlen. array9 acc Hlen.
  unfold native_suffix5, native_suffix6, native_round.
  do 8 plain_product. do 7 plain_carry. do 9 plain_carry.
  do 8 plain_product. do 15 plain_carry.
  exact_tails.
Qed.
Print Assumptions round5_decomposition.
Theorem round6_decomposition out a b acc : length acc = 9%nat ->
  native_suffix6 out a b acc = native_suffix7 out a b (native_round (f_index a (6:t_usize)) b acc).
Proof.
  intros Hlen. array9 acc Hlen.
  unfold native_suffix6, native_suffix7, native_round.
  do 8 plain_product. do 7 plain_carry. do 9 plain_carry.
  do 8 plain_product. do 15 plain_carry.
  exact_tails.
Qed.
Print Assumptions round6_decomposition.
Theorem round7_decomposition out a b acc : length acc = 9%nat ->
  native_suffix7 out a b acc = native_final out (native_round (f_index a (7:t_usize)) b acc).
Proof.
  intros Hlen. array9 acc Hlen.
  unfold native_suffix7, native_final, native_round.
  do 8 plain_product. do 7 plain_carry. do 9 plain_carry.
  do 8 plain_product. do 15 plain_carry.
  exact_tails.
Qed.
Print Assumptions round7_decomposition.
Theorem initial_tail_decomposition out a b state : length (fst state) = 8%nat ->
  native_after_redc out a b state =
  native_suffix1 out a b (fst state ++ [(cast (snd state) : t_u32)]).
Proof.
  destruct state as [words c]. cbn [fst snd]. intros Hlen. array8 words Hlen.
  unfold native_after_redc, native_suffix1. cbn [fst snd app]. reflexivity.
Qed.
Print Assumptions initial_tail_decomposition.
