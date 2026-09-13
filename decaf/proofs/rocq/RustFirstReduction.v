(* Handwritten native-prefix proofs. Full multiplication remains open. *)
From Stdlib Require Import ZArith Lia List.
From Core Require Import Core Carry RustMultiply RustFiatPrimitives RustFieldAdd RustMultiplyWords.
From Slice Require Import Decaf_proof_slice_Fiat NativeMultiplyPrefix.
Import ListNotations.
Open Scope Z_scope.
From Core Require Import RustMultiplyRow.

Theorem first_redc_decomposition out a b row :
  native_remainder out a b row = native_after_redc out a b (native_redc_state row).
Proof.
  do 9 (let w := fresh "word" in destruct row as [|w row]; [reflexivity|]).
  destruct row; [|reflexivity].
  unfold native_remainder, native_after_redc, native_redc_state.
  do 8 (match goal with |- context[fq_mulx_u32 ?o1 ?o2 ?x ?y] =>
    destruct (fq_mulx_u32 o1 o2 x y); cbn beta iota zeta end).
  do 15 (match goal with |- context[fq_addcarryx_u32 ?o1 ?o2 ?c ?x ?y] =>
    destruct (fq_addcarryx_u32 o1 o2 c x y); cbn beta iota zeta end).
  cbn [fst snd].
  match goal with |- ?left = ?right =>
    tryif constr_eq left right then reflexivity else fail "reduction tails differ syntactically"
  end.
Qed.

Theorem first_redc_correct row :
  length row = 9%nat -> Forall U32.canonical row ->
  4294967296 * limbs_value (redc_words row) =
    limbs_value row + fq_modulus * ((- U32.raw (nth 0 row (0 : t_u32))) mod 4294967296).
Proof.
  intros Hlen Hcan.
  do 9 (let w := fresh "word" in destruct row as [|w row]; [cbn in Hlen; discriminate|]).
  destruct row; [|cbn in Hlen; discriminate].
  repeat match goal with H : Forall _ (_::_) |- _ => inversion H; subst; clear H end.
  unfold redc_words, native_redc_state. cbn [nth].
  do 8 row_product.
  change (2^32) with 4294967296 in *.
  change (U32.raw (4294967295 : t_u32)) with 4294967295 in *.
  change (U32.raw (313222494 : t_u32)) with 313222494 in *.
  change (U32.raw (2586617174 : t_u32)) with 2586617174 in *.
  change (U32.raw (1622428958 : t_u32)) with 1622428958 in *.
  change (U32.raw (1547153409 : t_u32)) with 1547153409 in *.
  change (U32.raw (1504343806 : t_u32)) with 1504343806 in *.
  change (U32.raw (3489660929 : t_u32)) with 3489660929 in *.
  change (U32.raw (168919040 : t_u32)) with 168919040 in *.
  match goal with H : U32.raw ?lo + 4294967296 * U32.raw ?hi = U32.raw ?x * 4294967295 |- _ =>
    assert (Hm : U32.raw lo = (- U32.raw x) mod 4294967296) by
      (replace (- U32.raw x) with (U32.raw lo + (U32.raw hi - U32.raw x) * 4294967296) by lia;
       rewrite Z.mod_add by lia; symmetry; apply Z.mod_small; assumption);
    rewrite <- Hm
  end.
  do 6 row_carry.
  match goal with |- context[f_add (cast ?c) ?hi] =>
    remember (f_add (cast c : t_u32) hi) as top eqn:Etop;
    assert (Htop : U32.canonical top) by (subst top; apply add_word_canonical);
    assert (Hadd : U32.raw top = U8.raw c + U32.raw hi) by
      (subst top;
       change ((U8.raw c mod 4294967296 + U32.raw hi) mod 4294967296 = U8.raw c + U32.raw hi);
       rewrite (Z.mod_small (U8.raw c) 4294967296) by lia;
       apply Z.mod_small; lia)
  end.
  match goal with |- context[fq_addcarryx_u32 ?o1 ?o2 ?c ?x ?y] =>
    pose proof (addcarry_reconstruction o1 o2 c x y ltac:(row_word_bound)
      ltac:(row_word_bound) ltac:(row_word_bound)) as Hdiscard;
    destruct (fq_addcarryx_u32 o1 o2 c x y) as [discard carry];
    cbn [fst snd] in Hdiscard; destruct Hdiscard as [Hd [Hc He]];
    change (U8.raw (0 : t_u8)) with 0 in *;
    assert (Hz : U32.raw discard = 0) by (unfold U32.canonical, F32.width in *; lia);
    cbn beta iota zeta
  end.
  do 8 row_carry.
  cbn [fst snd app limbs_value].
  rewrite cast_carry_value by assumption.
  unfold fq_modulus.
  change (2^32) with 4294967296 in *.
  change (U8.raw (0 : t_u8)) with 0 in *.
  clear Etop Hlen Hm.
  repeat match goal with H : _ |- _ => progress (ring_simplify in H) end.
  ring_simplify.
  lia.
Qed.

Theorem first_redc_length row : length row = 9%nat ->
  length (redc_words row) = 9%nat.
Proof.
  intros Hlen.
  do 9 (let w := fresh "word" in destruct row as [|w row]; [cbn in Hlen; discriminate|]).
  destruct row; [|cbn in Hlen; discriminate].
  unfold redc_words, native_redc_state.
  do 8 (match goal with |- context[fq_mulx_u32 ?o1 ?o2 ?x ?y] =>
    destruct (fq_mulx_u32 o1 o2 x y); cbn beta iota zeta end).
  do 15 (match goal with |- context[fq_addcarryx_u32 ?o1 ?o2 ?c ?x ?y] =>
    destruct (fq_addcarryx_u32 o1 o2 c x y); cbn beta iota zeta end).
  reflexivity.
Qed.

Theorem first_redc_words row : length row = 9%nat ->
  Forall U32.canonical row -> Forall U32.canonical (redc_words row).
Proof.
  intros Hlen Hcan.
  do 9 (let w := fresh "word" in destruct row as [|w row]; [cbn in Hlen; discriminate|]).
  destruct row; [|cbn in Hlen; discriminate].
  repeat match goal with H : Forall _ (_::_) |- _ => inversion H; subst; clear H end.
  unfold redc_words, native_redc_state.
  do 8 row_product.
  do 6 row_carry.
  match goal with |- context[f_add (cast ?c) ?hi] =>
    remember (f_add (cast c : t_u32) hi) as top eqn:Etop;
    assert (Htop : U32.canonical top) by (subst top; apply add_word_canonical)
  end.
  do 9 row_carry.
  cbn [fst snd app].
  repeat (apply Forall_cons; [first [assumption | apply cast_carry_canonical] |]).
  apply Forall_nil.
Qed.

Theorem first_redc_bound row : length row = 9%nat ->
  Forall U32.canonical row ->
  0 <= limbs_value row < (4294967296 + 1) * fq_modulus ->
  0 <= limbs_value (redc_words row) < 2 * fq_modulus.
Proof.
  intros Hlen Hcan Hbound.
  pose proof (first_redc_correct row Hlen Hcan) as Heq.
  pose proof (Z.mod_pos_bound (- U32.raw (nth 0 row (0 : t_u32)))
    4294967296 ltac:(lia)) as Hm.
  unfold fq_modulus in *. lia.
Qed.

Theorem nine_words_top_zero xs : length xs = 9%nat ->
  Forall U32.canonical xs ->
  0 <= limbs_value xs < 2 * fq_modulus ->
  U32.raw (nth 8 xs (0 : t_u32)) = 0.
Proof.
  intros Hlen Hcan Hbound.
  do 9 (let w := fresh "word" in destruct xs as [|w xs]; [cbn in Hlen; discriminate|]).
  destruct xs; [|cbn in Hlen; discriminate].
  repeat match goal with H : Forall _ (_::_) |- _ => inversion H; subst; clear H end.
  cbn [nth]. cbn [limbs_value] in Hbound.
  unfold U32.canonical, F32.width in *.
  unfold fq_modulus in Hbound.
  lia.
Qed.

Theorem first_redc_top_zero row : length row = 9%nat ->
  Forall U32.canonical row ->
  0 <= limbs_value row < (4294967296 + 1) * fq_modulus ->
  U32.raw (nth 8 (redc_words row) (0 : t_u32)) = 0.
Proof.
  intros Hlen Hcan Hbound.
  apply nine_words_top_zero.
  - now apply first_redc_length.
  - now apply first_redc_words.
  - now apply first_redc_bound.
Qed.

Theorem redc_state_length row : length row = 9%nat ->
  length (fst (native_redc_state row)) = 8%nat.
Proof.
  intros Hlen. pose proof (first_redc_length row Hlen) as H.
  unfold redc_words in H. rewrite app_length in H. cbn in H. lia.
Qed.

Theorem redc_state_carry row : length row = 9%nat -> Forall U32.canonical row ->
  0 <= U8.raw (snd (native_redc_state row)) <= 1.
Proof.
  intros Hlen Hcan.
  do 9 (let w := fresh "word" in destruct row as [|w row]; [cbn in Hlen; discriminate|]).
  destruct row; [|cbn in Hlen; discriminate].
  repeat match goal with H : Forall _ (_::_) |- _ => inversion H; subst; clear H end.
  unfold native_redc_state.
  do 8 row_product. do 6 row_carry.
  match goal with |- context[f_add (cast ?c) ?hi] =>
    remember (f_add (cast c : t_u32) hi) as top eqn:Etop;
    assert (Htop : U32.canonical top) by (subst top; apply add_word_canonical)
  end.
  do 9 row_carry. cbn [snd]. assumption.
Qed.
