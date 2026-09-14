From Stdlib Require Import ZArith Lia List.
From Core Require Import Core Carry RustMultiply RustFiatPrimitives RustFieldAdd RustMultiplyWords RustMultiplyRow RustMultiplyRound.
From Slice Require Import Decaf_proof_slice_Fiat NativeMultiplyPrefix.
From FrSlice Require Import Decaf_fr_slice_Fiat.
Require Import FrPrefix FrHelpers FrFirstReduction FrReductionBounds FrRoundDefinition.
Import ListNotations.
Open Scope Z_scope.
Lemma fr_add9_same : fr_native_add9 = native_add9.
Proof. unfold fr_native_add9, native_add9. rewrite !fr_carry_same. reflexivity. Qed.
Theorem fr_add9_correct a b : length a = 9%nat -> length b = 9%nat ->
  Forall U32.canonical a -> Forall U32.canonical b ->
  let result := fr_native_add9 a b in
  length (fst result) = 9%nat /\ Forall U32.canonical (fst result) /\
  0 <= U8.raw (snd result) <= 1 /\
  limbs_value (fst result) + 4294967296 ^ 9 * U8.raw (snd result) =
    limbs_value a + limbs_value b.
Proof. rewrite fr_add9_same. apply add9_correct. Qed.
Theorem fr_round_product_decomposition digit b acc : length acc = 9%nat ->
  fr_native_round digit b acc = fr_round_after_product acc (native_first_row (digit_input digit) b).
Proof.
  intros Ha. array9 acc Ha.
  unfold fr_native_round, fr_round_after_product, native_first_row, digit_input.
  change (f_index [digit; (0:t_u32); (0:t_u32); (0:t_u32); (0:t_u32); (0:t_u32); (0:t_u32); (0:t_u32)] (0:t_usize)) with digit.
  rewrite !fr_multiply_same, !fr_carry_same.
  do 8 plain_product. do 7 plain_carry. exact_tails.
Qed.
Theorem fr_round_sum_decomposition acc row : length acc = 9%nat -> length row = 9%nat ->
  fr_round_after_product acc row = fr_round_after_sum (fr_native_add9 acc row).
Proof.
  intros Ha Hr. array9 acc Ha. array9 row Hr.
  unfold fr_round_after_product, fr_round_after_sum, fr_native_add9.
  rewrite !fr_multiply_same, !fr_carry_same.
  do 9 plain_carry. exact_tails.
Qed.
Theorem fr_round_redc_decomposition row carry : length row = 9%nat ->
  fr_round_after_sum (row, carry) = round_finish (fr_native_redc_state row) carry.
Proof.
  intros Hr. array9 row Hr.
  unfold fr_round_after_sum, round_finish, fr_native_redc_state.
  cbn [fst snd].
  rewrite !fr_multiply_same, !fr_carry_same.
  do 9 plain_product. do 16 plain_carry. exact_tails.
Qed.
Theorem fr_round_correct digit b acc :
  U32.canonical digit -> length b = 8%nat -> length acc = 9%nat ->
  Forall U32.canonical b -> Forall U32.canonical acc ->
  exists m, 0 <= m < 4294967296 /\
    4294967296 * limbs_value (fr_native_round digit b acc) =
      limbs_value acc + U32.raw digit * limbs_value b + fr_modulus * m.
Proof.
  intros Hd Hb Ha Hcb Hca.
  assert (Hdigit : Forall U32.canonical (digit_input digit)).
  { unfold digit_input. repeat (apply Forall_cons; [row_word_bound|]). apply Forall_nil. }
  set (product := native_first_row (digit_input digit) b).
  pose proof (first_row_length (digit_input digit) b) as Hplen. fold product in Hplen.
  pose proof (first_row_words (digit_input digit) b eq_refl Hb Hdigit Hcb) as Hpcan. fold product in Hpcan.
  pose proof (first_row_correct (digit_input digit) b eq_refl Hb Hdigit Hcb) as Hpvalue.
  fold product in Hpvalue. cbn [digit_input nth] in Hpvalue.
  pose proof (fr_add9_correct acc product Ha Hplen Hca Hpcan) as Hsum.
  destruct (fr_native_add9 acc product) as [sum carry] eqn:Es.
  cbn [fst snd] in Hsum. destruct Hsum as [Hslen [Hscan [Hcarry Hsvalue]]].
  rewrite fr_round_product_decomposition by assumption. fold product.
  rewrite fr_round_sum_decomposition by assumption. rewrite Es.
  rewrite fr_round_redc_decomposition by assumption.
  pose proof (finish_value (fr_native_redc_state sum) carry
    (fr_redc_state_length sum Hslen) (fr_redc_state_carry sum Hslen Hscan) Hcarry) as Hfinish.
  change (limbs_value (round_finish (fr_native_redc_state sum) carry) =
    limbs_value (fr_redc_words sum) + 4294967296 ^ 8 * U8.raw carry) in Hfinish.
  rewrite Hfinish.
  pose proof (fr_first_redc_correct sum Hslen Hscan) as Hredc.
  exists ((U32.raw (nth 0 sum (0:t_u32)) * 1893980673) mod 4294967296).
  split; [apply Z.mod_pos_bound; lia|].
  rewrite Z.mul_add_distr_l, Hredc.
  rewrite <- Hpvalue, <- Hsvalue.
  ring_simplify.
  reflexivity.
Qed.
Theorem fr_round_shape digit b acc :
  U32.canonical digit -> length b = 8%nat -> length acc = 9%nat ->
  Forall U32.canonical b -> Forall U32.canonical acc ->
  length (fr_native_round digit b acc) = 9%nat /\
  Forall U32.canonical (fr_native_round digit b acc).
Proof.
  intros Hd Hb Ha Hcb Hca.
  assert (Hdigit : Forall U32.canonical (digit_input digit)).
  { unfold digit_input. repeat (apply Forall_cons; [row_word_bound|]). apply Forall_nil. }
  set (product := native_first_row (digit_input digit) b).
  pose proof (first_row_length (digit_input digit) b) as Hplen. fold product in Hplen.
  pose proof (first_row_words (digit_input digit) b eq_refl Hb Hdigit Hcb) as Hpcan. fold product in Hpcan.
  pose proof (fr_add9_correct acc product Ha Hplen Hca Hpcan) as Hsum.
  destruct (fr_native_add9 acc product) as [sum carry] eqn:Es.
  cbn [fst snd] in Hsum. destruct Hsum as [Hslen [Hscan [Hcarry Hsvalue]]].
  rewrite fr_round_product_decomposition by assumption. fold product.
  rewrite fr_round_sum_decomposition by assumption. rewrite Es.
  rewrite fr_round_redc_decomposition by assumption.
  unfold round_finish. split.
  - rewrite app_length, (fr_redc_state_length sum Hslen). reflexivity.
  - apply Forall_app. split.
    + pose proof (fr_first_redc_words sum Hslen Hscan) as Hwords.
      unfold fr_redc_words in Hwords. apply Forall_app in Hwords. exact (proj1 Hwords).
    + apply Forall_cons; [apply add_word_canonical|apply Forall_nil].
Qed.
Theorem fr_round_bound digit b acc :
  U32.canonical digit -> length b = 8%nat -> length acc = 9%nat ->
  Forall U32.canonical b -> Forall U32.canonical acc ->
  0 <= limbs_value b < fr_modulus -> 0 <= limbs_value acc < 2 * fr_modulus ->
  0 <= limbs_value (fr_native_round digit b acc) < 2 * fr_modulus.
Proof.
  intros Hd Hb Ha Hcb Hca Hbv Hav.
  destruct (fr_round_correct digit b acc Hd Hb Ha Hcb Hca) as [m [Hm Heq]].
  unfold U32.canonical, F32.width in Hd.
  unfold fr_modulus in *. nia.
Qed.
Theorem fr_round_top_zero digit b acc :
  U32.canonical digit -> length b = 8%nat -> length acc = 9%nat ->
  Forall U32.canonical b -> Forall U32.canonical acc ->
  0 <= limbs_value b < fr_modulus -> 0 <= limbs_value acc < 2 * fr_modulus ->
  U32.raw (nth 8 (fr_native_round digit b acc) (0:t_u32)) = 0.
Proof.
  intros Hd Hb Ha Hcb Hca Hbv Hav.
  destruct (fr_round_shape digit b acc Hd Hb Ha Hcb Hca) as [Hlen Hcan].
  apply fr_nine_words_top_zero; try assumption.
  now apply fr_round_bound.
Qed.
Print Assumptions fr_add9_same.
Print Assumptions fr_add9_correct.
Print Assumptions fr_round_product_decomposition.
Print Assumptions fr_round_sum_decomposition.
Print Assumptions fr_round_redc_decomposition.
Print Assumptions fr_round_correct.
Print Assumptions fr_round_shape.
Print Assumptions fr_round_bound.
Print Assumptions fr_round_top_zero.
