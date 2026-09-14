From Stdlib Require Import ZArith Lia List.
From Core Require Import Core Carry RustMultiply RustFiatPrimitives RustFieldAdd RustMultiplyWords RustMultiplyRow RustMultiplyRound.
From Slice Require Import Decaf_proof_slice_Fiat NativeMultiplyPrefix.
From FrSlice Require Import Decaf_fr_slice_Fiat.
Require Import FrPrefix FrHelpers FrFirstReduction FrReductionBounds FrRoundDefinition FrRound FrFinalDefinition FrAfterReductionDefinition.
Import ListNotations.
Open Scope Z_scope.
Ltac fr_plain_product := match goal with |- context[fr_mulx_u32 ?o1 ?o2 ?x ?y] => destruct (fr_mulx_u32 o1 o2 x y); cbn beta iota zeta end.
Ltac fr_plain_carry := match goal with |- context[fr_addcarryx_u32 ?o1 ?o2 ?c ?x ?y] => destruct (fr_addcarryx_u32 o1 o2 c x y); cbn beta iota zeta end.
Require Import FrSuffixDefinition1 FrSuffixDefinition2 FrSuffixDefinition3 FrSuffixDefinition4 FrSuffixDefinition5 FrSuffixDefinition6 FrSuffixDefinition7.
Theorem fr_first_redc_decomposition out a b row :
  fr_native_remainder out a b row = fr_native_after_redc out a b (fr_native_redc_state row).
Proof.
  do 9 (let w := fresh "word" in destruct row as [|w row]; [reflexivity|]).
  destruct row; [|reflexivity].
  unfold fr_native_remainder, fr_native_after_redc, fr_native_redc_state.
  do 9 (match goal with |- context[fr_mulx_u32 ?o1 ?o2 ?x ?y] =>
    destruct (fr_mulx_u32 o1 o2 x y); cbn beta iota zeta end).
  do 16 (match goal with |- context[fr_addcarryx_u32 ?o1 ?o2 ?c ?x ?y] =>
    destruct (fr_addcarryx_u32 o1 o2 c x y); cbn beta iota zeta end).
  cbn [fst snd].
  match goal with |- ?left = ?right =>
    tryif constr_eq left right then reflexivity else fail "reduction tails differ syntactically"
  end.
Qed.
Print Assumptions fr_first_redc_decomposition.
Theorem fr_round1_decomposition out a b acc : length acc = 9%nat ->
  fr_native_suffix1 out a b acc = fr_native_suffix2 out a b (fr_native_round (f_index a (1:t_usize)) b acc).
Proof.
  intros Hlen. array9 acc Hlen.
  unfold fr_native_suffix1, fr_native_suffix2, fr_native_round.
  do 8 fr_plain_product. do 7 fr_plain_carry. do 9 fr_plain_carry.
  do 9 fr_plain_product. do 16 fr_plain_carry.
  exact_tails.
Qed.
Print Assumptions fr_round1_decomposition.
Theorem fr_round2_decomposition out a b acc : length acc = 9%nat ->
  fr_native_suffix2 out a b acc = fr_native_suffix3 out a b (fr_native_round (f_index a (2:t_usize)) b acc).
Proof.
  intros Hlen. array9 acc Hlen.
  unfold fr_native_suffix2, fr_native_suffix3, fr_native_round.
  do 8 fr_plain_product. do 7 fr_plain_carry. do 9 fr_plain_carry.
  do 9 fr_plain_product. do 16 fr_plain_carry.
  exact_tails.
Qed.
Print Assumptions fr_round2_decomposition.
Theorem fr_round3_decomposition out a b acc : length acc = 9%nat ->
  fr_native_suffix3 out a b acc = fr_native_suffix4 out a b (fr_native_round (f_index a (3:t_usize)) b acc).
Proof.
  intros Hlen. array9 acc Hlen.
  unfold fr_native_suffix3, fr_native_suffix4, fr_native_round.
  do 8 fr_plain_product. do 7 fr_plain_carry. do 9 fr_plain_carry.
  do 9 fr_plain_product. do 16 fr_plain_carry.
  exact_tails.
Qed.
Print Assumptions fr_round3_decomposition.
Theorem fr_round4_decomposition out a b acc : length acc = 9%nat ->
  fr_native_suffix4 out a b acc = fr_native_suffix5 out a b (fr_native_round (f_index a (4:t_usize)) b acc).
Proof.
  intros Hlen. array9 acc Hlen.
  unfold fr_native_suffix4, fr_native_suffix5, fr_native_round.
  do 8 fr_plain_product. do 7 fr_plain_carry. do 9 fr_plain_carry.
  do 9 fr_plain_product. do 16 fr_plain_carry.
  exact_tails.
Qed.
Print Assumptions fr_round4_decomposition.
Theorem fr_round5_decomposition out a b acc : length acc = 9%nat ->
  fr_native_suffix5 out a b acc = fr_native_suffix6 out a b (fr_native_round (f_index a (5:t_usize)) b acc).
Proof.
  intros Hlen. array9 acc Hlen.
  unfold fr_native_suffix5, fr_native_suffix6, fr_native_round.
  do 8 fr_plain_product. do 7 fr_plain_carry. do 9 fr_plain_carry.
  do 9 fr_plain_product. do 16 fr_plain_carry.
  exact_tails.
Qed.
Print Assumptions fr_round5_decomposition.
Theorem fr_round6_decomposition out a b acc : length acc = 9%nat ->
  fr_native_suffix6 out a b acc = fr_native_suffix7 out a b (fr_native_round (f_index a (6:t_usize)) b acc).
Proof.
  intros Hlen. array9 acc Hlen.
  unfold fr_native_suffix6, fr_native_suffix7, fr_native_round.
  do 8 fr_plain_product. do 7 fr_plain_carry. do 9 fr_plain_carry.
  do 9 fr_plain_product. do 16 fr_plain_carry.
  exact_tails.
Qed.
Print Assumptions fr_round6_decomposition.
Theorem fr_round7_decomposition out a b acc : length acc = 9%nat ->
  fr_native_suffix7 out a b acc = fr_native_final out (fr_native_round (f_index a (7:t_usize)) b acc).
Proof.
  intros Hlen. array9 acc Hlen.
  unfold fr_native_suffix7, fr_native_final, fr_native_round.
  do 8 fr_plain_product. do 7 fr_plain_carry. do 9 fr_plain_carry.
  do 9 fr_plain_product. do 16 fr_plain_carry.
  exact_tails.
Qed.
Print Assumptions fr_round7_decomposition.
Theorem fr_initial_tail_decomposition out a b state : length (fst state) = 8%nat ->
  fr_native_after_redc out a b state =
  fr_native_suffix1 out a b (fst state ++ [(cast (snd state) : t_u32)]).
Proof.
  destruct state as [words c]. cbn [fst snd]. intros Hlen. array8 words Hlen.
  unfold fr_native_after_redc, fr_native_suffix1. cbn [fst snd app]. reflexivity.
Qed.
Print Assumptions fr_initial_tail_decomposition.
