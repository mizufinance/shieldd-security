(* Native repeated-round composition; full multiplication remains open. *)
From Stdlib Require Import ZArith Lia List.
From Core Require Import Core Carry RustMultiply RustFiatPrimitives RustFieldAdd RustMultiplyWords RustMultiplyRow RustFirstReduction.
From Slice Require Import Decaf_proof_slice_Fiat NativeMultiplyPrefix.
Import ListNotations.
Open Scope Z_scope.

Theorem add9_correct a b : length a = 9%nat -> length b = 9%nat ->
  Forall U32.canonical a -> Forall U32.canonical b ->
  let result := native_add9 a b in
  length (fst result) = 9%nat /\ Forall U32.canonical (fst result) /\
  0 <= U8.raw (snd result) <= 1 /\
  limbs_value (fst result) + 4294967296 ^ 9 * U8.raw (snd result) =
    limbs_value a + limbs_value b.
Proof.
  intros Ha Hb Hca Hcb.
  do 9 (let w := fresh "word" in destruct a as [|w a]; [cbn in Ha; discriminate|]).
  destruct a; [|cbn in Ha; discriminate].
  do 9 (let w := fresh "word" in destruct b as [|w b]; [cbn in Hb; discriminate|]).
  destruct b; [|cbn in Hb; discriminate].
  repeat match goal with H : Forall _ (_::_) |- _ => inversion H; subst; clear H end.
  unfold native_add9. do 9 row_carry.
  cbn [fst snd].
  split; [reflexivity|].
  split.
  - repeat (apply Forall_cons; [assumption|]). apply Forall_nil.
  - split; [assumption|].
    cbn [limbs_value].
    change (2^32) with 4294967296 in *.
    change (U8.raw (0 : t_u8)) with 0 in *.
    lia.
Qed.

Ltac array9 xs Hlen :=
  do 9 (let w := fresh "word" in destruct xs as [|w xs]; [cbn in Hlen; discriminate|]);
  destruct xs; [|cbn in Hlen; discriminate].
Ltac plain_product := (match goal with |- context[fq_mulx_u32 ?o1 ?o2 ?x ?y] =>
  destruct (fq_mulx_u32 o1 o2 x y); cbn beta iota zeta end).
Ltac plain_carry := (match goal with |- context[fq_addcarryx_u32 ?o1 ?o2 ?c ?x ?y] =>
  destruct (fq_addcarryx_u32 o1 o2 c x y); cbn beta iota zeta end).
Ltac exact_tails := cbn [fst snd app];
  match goal with |- ?left = ?right =>
    tryif constr_eq left right then reflexivity else fail "round tails differ syntactically"
  end.

Theorem round_product_decomposition digit b acc : length acc = 9%nat ->
  native_round digit b acc = round_after_product acc (native_first_row (digit_input digit) b).
Proof.
  intros Ha. array9 acc Ha.
  unfold native_round, round_after_product, native_first_row, digit_input.
  change (f_index [digit; (0:t_u32); (0:t_u32); (0:t_u32); (0:t_u32); (0:t_u32); (0:t_u32); (0:t_u32)] (0:t_usize)) with digit.
  do 8 plain_product. do 7 plain_carry. exact_tails.
Qed.

Theorem round_sum_decomposition acc row : length acc = 9%nat -> length row = 9%nat ->
  round_after_product acc row = round_after_sum (native_add9 acc row).
Proof.
  intros Ha Hr. array9 acc Ha. array9 row Hr.
  unfold round_after_product, round_after_sum, native_add9.
  do 9 plain_carry. exact_tails.
Qed.

Theorem round_redc_decomposition row carry : length row = 9%nat ->
  round_after_sum (row, carry) = round_finish (native_redc_state row) carry.
Proof.
  intros Hr. array9 row Hr.
  unfold round_after_sum, round_finish, native_redc_state.
  cbn [fst snd].
  do 8 plain_product. do 15 plain_carry. exact_tails.
Qed.

Theorem finish_value state carry : length (fst state) = 8%nat ->
  0 <= U8.raw (snd state) <= 1 -> 0 <= U8.raw carry <= 1 ->
  limbs_value (round_finish state carry) =
  limbs_value (fst state ++ [(cast (snd state) : t_u32)]) +
    4294967296 ^ 8 * U8.raw carry.
Proof.
  destruct state as [words c]. cbn [fst snd]. intros Hlen Hc Hd.
  array8 words Hlen.
  unfold round_finish. cbn [fst snd app limbs_value].
  match goal with |- context[U32.raw ?term] =>
    lazymatch term with context[f_add _ _] =>
      assert (Hadd : U32.raw term = U8.raw c + U8.raw carry) by
        (change (((U8.raw c mod 4294967296 + U8.raw carry mod 4294967296) mod 4294967296)
          = U8.raw c + U8.raw carry);
         rewrite (Z.mod_small (U8.raw c) 4294967296),
           (Z.mod_small (U8.raw carry) 4294967296) by lia;
         apply Z.mod_small; lia);
      rewrite Hadd
    end
  end.
  rewrite cast_carry_value by assumption. ring.
Qed.

Theorem round_correct digit b acc :
  U32.canonical digit -> length b = 8%nat -> length acc = 9%nat ->
  Forall U32.canonical b -> Forall U32.canonical acc ->
  exists m, 0 <= m < 4294967296 /\
    4294967296 * limbs_value (native_round digit b acc) =
      limbs_value acc + U32.raw digit * limbs_value b + fq_modulus * m.
Proof.
  intros Hd Hb Ha Hcb Hca.
  assert (Hdigit : Forall U32.canonical (digit_input digit)).
  { unfold digit_input. repeat (apply Forall_cons; [row_word_bound|]). apply Forall_nil. }
  set (product := native_first_row (digit_input digit) b).
  pose proof (first_row_length (digit_input digit) b) as Hplen. fold product in Hplen.
  pose proof (first_row_words (digit_input digit) b eq_refl Hb Hdigit Hcb) as Hpcan. fold product in Hpcan.
  pose proof (first_row_correct (digit_input digit) b eq_refl Hb Hdigit Hcb) as Hpvalue.
  fold product in Hpvalue. cbn [digit_input nth] in Hpvalue.
  pose proof (add9_correct acc product Ha Hplen Hca Hpcan) as Hsum.
  destruct (native_add9 acc product) as [sum carry] eqn:Es.
  cbn [fst snd] in Hsum. destruct Hsum as [Hslen [Hscan [Hcarry Hsvalue]]].
  rewrite round_product_decomposition by assumption. fold product.
  rewrite round_sum_decomposition by assumption. rewrite Es.
  rewrite round_redc_decomposition by assumption.
  pose proof (finish_value (native_redc_state sum) carry
    (redc_state_length sum Hslen) (redc_state_carry sum Hslen Hscan) Hcarry) as Hfinish.
  change (limbs_value (round_finish (native_redc_state sum) carry) =
    limbs_value (redc_words sum) + 4294967296 ^ 8 * U8.raw carry) in Hfinish.
  rewrite Hfinish.
  pose proof (first_redc_correct sum Hslen Hscan) as Hredc.
  exists ((- U32.raw (nth 0 sum (0:t_u32))) mod 4294967296).
  split; [apply Z.mod_pos_bound; lia|].
  rewrite Z.mul_add_distr_l, Hredc.
  rewrite <- Hpvalue, <- Hsvalue.
  ring_simplify.
  reflexivity.
Qed.

Theorem round_shape digit b acc :
  U32.canonical digit -> length b = 8%nat -> length acc = 9%nat ->
  Forall U32.canonical b -> Forall U32.canonical acc ->
  length (native_round digit b acc) = 9%nat /\
  Forall U32.canonical (native_round digit b acc).
Proof.
  intros Hd Hb Ha Hcb Hca.
  assert (Hdigit : Forall U32.canonical (digit_input digit)).
  { unfold digit_input. repeat (apply Forall_cons; [row_word_bound|]). apply Forall_nil. }
  set (product := native_first_row (digit_input digit) b).
  pose proof (first_row_length (digit_input digit) b) as Hplen. fold product in Hplen.
  pose proof (first_row_words (digit_input digit) b eq_refl Hb Hdigit Hcb) as Hpcan. fold product in Hpcan.
  pose proof (add9_correct acc product Ha Hplen Hca Hpcan) as Hsum.
  destruct (native_add9 acc product) as [sum carry] eqn:Es.
  cbn [fst snd] in Hsum. destruct Hsum as [Hslen [Hscan [Hcarry Hsvalue]]].
  rewrite round_product_decomposition by assumption. fold product.
  rewrite round_sum_decomposition by assumption. rewrite Es.
  rewrite round_redc_decomposition by assumption.
  unfold round_finish. split.
  - rewrite app_length, (redc_state_length sum Hslen). reflexivity.
  - apply Forall_app. split.
    + pose proof (first_redc_words sum Hslen Hscan) as Hwords.
      unfold redc_words in Hwords. apply Forall_app in Hwords. exact (proj1 Hwords).
    + apply Forall_cons; [apply add_word_canonical|apply Forall_nil].
Qed.

Theorem round_bound digit b acc :
  U32.canonical digit -> length b = 8%nat -> length acc = 9%nat ->
  Forall U32.canonical b -> Forall U32.canonical acc ->
  0 <= limbs_value b < fq_modulus -> 0 <= limbs_value acc < 2 * fq_modulus ->
  0 <= limbs_value (native_round digit b acc) < 2 * fq_modulus.
Proof.
  intros Hd Hb Ha Hcb Hca Hbv Hav.
  destruct (round_correct digit b acc Hd Hb Ha Hcb Hca) as [m [Hm Heq]].
  unfold U32.canonical, F32.width in Hd.
  unfold fq_modulus in *. nia.
Qed.

Theorem round_top_zero digit b acc :
  U32.canonical digit -> length b = 8%nat -> length acc = 9%nat ->
  Forall U32.canonical b -> Forall U32.canonical acc ->
  0 <= limbs_value b < fq_modulus -> 0 <= limbs_value acc < 2 * fq_modulus ->
  U32.raw (nth 8 (native_round digit b acc) (0:t_u32)) = 0.
Proof.
  intros Hd Hb Ha Hcb Hca Hbv Hav.
  destruct (round_shape digit b acc Hd Hb Ha Hcb Hca) as [Hlen Hcan].
  apply nine_words_top_zero; try assumption.
  now apply round_bound.
Qed.
