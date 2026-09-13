(* Handwritten native-prefix proofs. Full multiplication remains open. *)
From Stdlib Require Import ZArith Lia List.
From Core Require Import Core Carry RustMultiply RustFiatPrimitives RustFieldAdd RustMultiplyWords.
From Slice Require Import Decaf_proof_slice_Fiat NativeMultiplyPrefix.
Import ListNotations.
Open Scope Z_scope.

Ltac row_word_bound := first [assumption |
  unfold U32.canonical, U32.raw, U32.of_Z, U8.raw, U8.of_Z, F32.width, F8.width; cbn; lia].

Ltac row_product :=
  match goal with |- context[fq_mulx_u32 ?o1 ?o2 ?x ?y] =>
    let H := fresh "product_equation" in let Hroom := fresh "product_room" in
    pose proof (multiply_reconstruction o1 o2 x y ltac:(row_word_bound) ltac:(row_word_bound)) as H;
    pose proof (multiply_high_room o1 o2 x y ltac:(row_word_bound) ltac:(row_word_bound)) as Hroom;
    let lo := fresh "product_low" in let hi := fresh "product_high" in
    destruct (fq_mulx_u32 o1 o2 x y) as [lo hi];
    cbn [fst snd] in H, Hroom; destruct H as [? [? ?]]; cbn beta iota zeta
  end.

Ltac row_carry :=
  match goal with |- context[fq_addcarryx_u32 ?o1 ?o2 ?c ?x ?y] =>
    let H := fresh "sum_equation" in
    pose proof (addcarry_reconstruction o1 o2 c x y ltac:(row_word_bound)
      ltac:(row_word_bound) ltac:(row_word_bound)) as H;
    let lo := fresh "sum_low" in let hi := fresh "sum_carry" in
    destruct (fq_addcarryx_u32 o1 o2 c x y) as [lo hi];
    cbn [fst snd] in H; destruct H as [? [? ?]]; cbn beta iota zeta
  end.

Theorem first_row_correct a b :
  length a = 8%nat -> length b = 8%nat ->
  Forall U32.canonical a -> Forall U32.canonical b ->
  limbs_value (native_first_row a b) = U32.raw (nth 0 a (0 : t_u32)) * limbs_value b.
Proof.
  intros Ha Hb Hca Hcb.
  array8 a Ha. array8 b Hb.
  repeat match goal with H : Forall _ (_::_) |- _ => inversion H; subst; clear H end.
  unfold native_first_row.
  unfold f_index.
  change (Z.to_nat (U64.value (0 : t_usize))) with 0%nat.
  change (Z.to_nat (U64.value (1 : t_usize))) with 1%nat.
  change (Z.to_nat (U64.value (2 : t_usize))) with 2%nat.
  change (Z.to_nat (U64.value (3 : t_usize))) with 3%nat.
  change (Z.to_nat (U64.value (4 : t_usize))) with 4%nat.
  change (Z.to_nat (U64.value (5 : t_usize))) with 5%nat.
  change (Z.to_nat (U64.value (6 : t_usize))) with 6%nat.
  change (Z.to_nat (U64.value (7 : t_usize))) with 7%nat.
  cbn [nth].
  do 8 row_product. do 7 row_carry.
  cbn [limbs_value].
  match goal with |- context[U32.raw (f_add (cast ?c) ?hi)] =>
    assert (Hadd : U32.raw (f_add (cast c : t_u32) hi) = U8.raw c + U32.raw hi)
      by (change ((U8.raw c mod 4294967296 + U32.raw hi) mod 4294967296 = U8.raw c + U32.raw hi);
          rewrite (Z.mod_small (U8.raw c) 4294967296) by lia;
          apply Z.mod_small; lia);
    rewrite Hadd
  end.
  change (2^32) with 4294967296 in *.
  change (U8.raw (0 : t_u8)) with 0 in *.
  clear Ha Hb Hadd.
  repeat match goal with H : U32.canonical _ |- _ => clear H end.
  repeat match goal with H : Forall _ _ |- _ => clear H end.
  repeat match goal with H : _ /\ _ |- _ => clear H end.
  repeat match goal with H : _ |- _ => progress (ring_simplify in H) end.
  ring_simplify.

  nia.
Qed.

Theorem first_row_decomposition out a b :
  fq_mul out a b = native_remainder out a b (native_first_row a b).
Proof.
  unfold fq_mul, native_remainder, native_first_row.
  do 8 (match goal with |- context[fq_mulx_u32 ?o1 ?o2 ?x ?y] =>
    destruct (fq_mulx_u32 o1 o2 x y); cbn beta iota zeta end).
  do 7 (match goal with |- context[fq_addcarryx_u32 ?o1 ?o2 ?c ?x ?y] =>
    destruct (fq_addcarryx_u32 o1 o2 c x y); cbn beta iota zeta end).
  reflexivity.
Qed.

Theorem first_row_length a b : length (native_first_row a b) = 9%nat.
Proof.
  unfold native_first_row.
  do 8 (match goal with |- context[fq_mulx_u32 ?o1 ?o2 ?x ?y] =>
    destruct (fq_mulx_u32 o1 o2 x y); cbn beta iota zeta end).
  do 7 (match goal with |- context[fq_addcarryx_u32 ?o1 ?o2 ?c ?x ?y] =>
    destruct (fq_addcarryx_u32 o1 o2 c x y); cbn beta iota zeta end).
  reflexivity.
Qed.

Theorem first_row_words a b :
  length a = 8%nat -> length b = 8%nat ->
  Forall U32.canonical a -> Forall U32.canonical b ->
  Forall U32.canonical (native_first_row a b).
Proof.
  intros Ha Hb Hca Hcb.
  array8 a Ha. array8 b Hb.
  repeat match goal with H : Forall _ (_::_) |- _ => inversion H; subst; clear H end.
  unfold native_first_row, f_index.
  change (Z.to_nat (U64.value (0 : t_usize))) with 0%nat.
  change (Z.to_nat (U64.value (1 : t_usize))) with 1%nat.
  change (Z.to_nat (U64.value (2 : t_usize))) with 2%nat.
  change (Z.to_nat (U64.value (3 : t_usize))) with 3%nat.
  change (Z.to_nat (U64.value (4 : t_usize))) with 4%nat.
  change (Z.to_nat (U64.value (5 : t_usize))) with 5%nat.
  change (Z.to_nat (U64.value (6 : t_usize))) with 6%nat.
  change (Z.to_nat (U64.value (7 : t_usize))) with 7%nat.
  cbn [nth].
  do 8 row_product. do 7 row_carry.
  repeat (apply Forall_cons; [first [assumption | apply add_word_canonical] |]).
  apply Forall_nil.
Qed.

