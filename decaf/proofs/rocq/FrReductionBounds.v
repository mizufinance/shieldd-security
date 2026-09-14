From Stdlib Require Import ZArith Lia List.
From Core Require Import Core Carry RustMultiply RustFiatPrimitives RustFieldAdd RustMultiplyWords RustMultiplyRow.
From Slice Require Import Decaf_proof_slice_Fiat.
From FrSlice Require Import Decaf_fr_slice_Fiat.
Require Import FrPrefix FrHelpers FrFirstReduction.
Import ListNotations.
Open Scope Z_scope.
Theorem fr_first_redc_length row : length row = 9%nat ->
  length (fr_redc_words row) = 9%nat.
Proof.
  intros Hlen.
  do 9 (let w := fresh "word" in destruct row as [|w row]; [cbn in Hlen; discriminate|]).
  destruct row; [|cbn in Hlen; discriminate].
  unfold fr_redc_words, fr_native_redc_state.
  rewrite !fr_multiply_same, !fr_carry_same.
  do 9 (match goal with |- context[fq_mulx_u32 ?o1 ?o2 ?x ?y] =>
    destruct (fq_mulx_u32 o1 o2 x y); cbn beta iota zeta end).
  do 16 (match goal with |- context[fq_addcarryx_u32 ?o1 ?o2 ?c ?x ?y] =>
    destruct (fq_addcarryx_u32 o1 o2 c x y); cbn beta iota zeta end).
  reflexivity.
Qed.

Theorem fr_first_redc_words row : length row = 9%nat ->
  Forall U32.canonical row -> Forall U32.canonical (fr_redc_words row).
Proof.
  intros Hlen Hcan.
  do 9 (let w := fresh "word" in destruct row as [|w row]; [cbn in Hlen; discriminate|]).
  destruct row; [|cbn in Hlen; discriminate].
  repeat match goal with H : Forall _ (_::_) |- _ => inversion H; subst; clear H end.
  unfold fr_redc_words, fr_native_redc_state.
  rewrite !fr_multiply_same, !fr_carry_same.
  do 9 row_product.
  do 7 row_carry.
  match goal with |- context[f_add (cast ?c) ?hi] =>
    remember (f_add (cast c : t_u32) hi) as top eqn:Etop;
    assert (Htop : U32.canonical top) by (subst top; apply add_word_canonical)
  end.
  do 9 row_carry.
  cbn [fst snd app].
  repeat (apply Forall_cons; [first [assumption | apply cast_carry_canonical] |]).
  apply Forall_nil.
Qed.

Theorem fr_first_redc_bound row : length row = 9%nat ->
  Forall U32.canonical row ->
  0 <= limbs_value row < (4294967296 + 1) * fr_modulus ->
  0 <= limbs_value (fr_redc_words row) < 2 * fr_modulus.
Proof.
  intros Hlen Hcan Hbound.
  pose proof (fr_first_redc_correct row Hlen Hcan) as Heq.
  pose proof (Z.mod_pos_bound (U32.raw (nth 0 row (0 : t_u32)) * 1893980673)
    4294967296 ltac:(lia)) as Hm.
  unfold fr_modulus in *. lia.
Qed.

Theorem fr_nine_words_top_zero xs : length xs = 9%nat ->
  Forall U32.canonical xs ->
  0 <= limbs_value xs < 2 * fr_modulus ->
  U32.raw (nth 8 xs (0 : t_u32)) = 0.
Proof.
  intros Hlen Hcan Hbound.
  do 9 (let w := fresh "word" in destruct xs as [|w xs]; [cbn in Hlen; discriminate|]).
  destruct xs; [|cbn in Hlen; discriminate].
  repeat match goal with H : Forall _ (_::_) |- _ => inversion H; subst; clear H end.
  cbn [nth]. cbn [limbs_value] in Hbound.
  unfold U32.canonical, F32.width in *.
  unfold fr_modulus in Hbound.
  lia.
Qed.

Theorem fr_first_redc_top_zero row : length row = 9%nat ->
  Forall U32.canonical row ->
  0 <= limbs_value row < (4294967296 + 1) * fr_modulus ->
  U32.raw (nth 8 (fr_redc_words row) (0 : t_u32)) = 0.
Proof.
  intros Hlen Hcan Hbound.
  apply fr_nine_words_top_zero.
  - now apply fr_first_redc_length.
  - now apply fr_first_redc_words.
  - now apply fr_first_redc_bound.
Qed.

Theorem fr_redc_state_length row : length row = 9%nat ->
  length (fst (fr_native_redc_state row)) = 8%nat.
Proof.
  intros Hlen. pose proof (fr_first_redc_length row Hlen) as H.
  unfold fr_redc_words in H. rewrite app_length in H. cbn in H. lia.
Qed.

Theorem fr_redc_state_carry row : length row = 9%nat -> Forall U32.canonical row ->
  0 <= U8.raw (snd (fr_native_redc_state row)) <= 1.
Proof.
  intros Hlen Hcan.
  do 9 (let w := fresh "word" in destruct row as [|w row]; [cbn in Hlen; discriminate|]).
  destruct row; [|cbn in Hlen; discriminate].
  repeat match goal with H : Forall _ (_::_) |- _ => inversion H; subst; clear H end.
  unfold fr_native_redc_state.
  rewrite !fr_multiply_same, !fr_carry_same.
  do 9 row_product. do 7 row_carry.
  match goal with |- context[f_add (cast ?c) ?hi] =>
    remember (f_add (cast c : t_u32) hi) as top eqn:Etop;
    assert (Htop : U32.canonical top) by (subst top; apply add_word_canonical)
  end.
  do 9 row_carry. cbn [snd]. assumption.
Qed.

Print Assumptions fr_first_redc_length.
Print Assumptions fr_first_redc_words.
Print Assumptions fr_first_redc_bound.
Print Assumptions fr_nine_words_top_zero.
Print Assumptions fr_first_redc_top_zero.
Print Assumptions fr_redc_state_length.
Print Assumptions fr_redc_state_carry.
