From Stdlib Require Import ZArith Lia List.
From Core Require Import Core Carry RustBorrow RustSelect RustMultiply RustArray.
From Slice Require Import Decaf_proof_slice_Fiat.
Import ListNotations.
Open Scope Z_scope.

Lemma add_word_canonical (x y : t_u32) : U32.canonical (f_add x y).
Proof.
  change (0 <= (U32.raw x + U32.raw y) mod 4294967296 < 4294967296).
  apply Z.mod_pos_bound. lia.
Qed.

Theorem mul_output_length out a b :
  length out = 8%nat -> length (fq_mul out a b) = 8%nat.
Proof.
  intros Ho.
  do 8 (let word := fresh "word" in destruct out as [|word out]; [cbn in Ho; discriminate|]).
  destruct out; [|cbn in Ho; discriminate].
  reflexivity.
Qed.

Theorem mul_accesses (out a b values : list t_u32) :
  length out = 8%nat -> length a = 8%nat -> length b = 8%nat ->
  Forall (index_defined a) indices8 /\
  Forall (index_defined b) indices8 /\
  writes_safe out (combine indices8 values).
Proof.
  intros. split; [apply indices8_safe; assumption|].
  split; [apply indices8_safe; assumption|].
  apply writes8_safe; assumption.
Qed.

Lemma cast_carry_canonical (c : t_u8) : U32.canonical (cast c : t_u32).
Proof.
  change (0 <= U8.raw c mod 4294967296 < 4294967296).
  apply Z.mod_pos_bound. lia.
Qed.

Ltac array8 xs Hlen :=
  do 8 (let x := fresh "limb" in destruct xs as [|x xs]; [cbn in Hlen; discriminate|]);
  destruct xs; [|cbn in Hlen; discriminate].

Ltac word_bound := first [assumption | apply cast_carry_canonical |
  apply add_word_canonical |
  unfold U32.canonical, U32.raw, U32.of_Z, U8.raw, U8.of_Z, F32.width, F8.width; cbn; lia].

Ltac native_step :=
  first [
    match goal with |- context[fq_mulx_u32 ?o1 ?o2 ?x ?y] =>
      let H := fresh "product_equation" in
      pose proof (multiply_reconstruction o1 o2 x y ltac:(word_bound) ltac:(word_bound)) as H;
      let lo := fresh "product_low" in let hi := fresh "product_high" in
      destruct (fq_mulx_u32 o1 o2 x y) as [lo hi];
      cbn [fst snd] in H; let unused := fresh "unused" in
      destruct H as [? [? unused]]; clear unused; cbn beta iota zeta
    end |
    match goal with |- context[fq_addcarryx_u32 ?o1 ?o2 ?c ?x ?y] =>
      let H := fresh "sum_equation" in
      pose proof (addcarry_reconstruction o1 o2 c x y ltac:(word_bound)
        ltac:(word_bound) ltac:(word_bound)) as H;
      let lo := fresh "sum_low" in let hi := fresh "sum_carry" in
      destruct (fq_addcarryx_u32 o1 o2 c x y) as [lo hi];
      cbn [fst snd] in H; let unused := fresh "unused" in
      destruct H as [? [? unused]]; clear unused; cbn beta iota zeta
    end |
    match goal with |- context[fq_subborrowx_u32 ?o1 ?o2 ?c ?x ?y] =>
      let H := fresh "difference_equation" in
      pose proof (borrow_reconstruction o1 o2 c x y ltac:(word_bound)
        ltac:(word_bound) ltac:(word_bound)) as H;
      let lo := fresh "difference_low" in let hi := fresh "difference_borrow" in
      destruct (fq_subborrowx_u32 o1 o2 c x y) as [lo hi];
      cbn [fst snd] in H; let unused := fresh "unused" in
      destruct H as [? [? unused]]; clear unused; cbn beta iota zeta
    end ].

Ltac drop_dead_words :=
  repeat match goal with x : t_u32 |- _ => clear dependent x end;
  repeat match goal with x : t_u8 |- _ => clear dependent x end.

Theorem mul_output_words out a b :
  length out = 8%nat -> length a = 8%nat -> length b = 8%nat ->
  Forall U32.canonical a -> Forall U32.canonical b ->
  Forall U32.canonical (fq_mul out a b).
Proof.
  intros Ho Ha Hb Hca Hcb.
  array8 out Ho. array8 a Ha. array8 b Hb.
  repeat match goal with H : Forall _ (_::_) |- _ => inversion H; subst; clear H end.
  unfold fq_mul.
  cbn [f_index nth U64.value U64.raw U64.of_Z F64.width F64.signed].
  repeat (native_step; drop_dead_words).
  repeat rewrite select_exact by word_bound.
  match goal with |- context[if U8.raw ?c =? 0 then _ else _] =>
    destruct (Z.eqb_spec (U8.raw c) 0)
  end.
  all: unfold update_at_usize, U64.value, U64.raw, U64.of_Z, F64.width, F64.signed.
  all: cbn -[Z.mul] in *.
  all: repeat (apply Forall_cons; [assumption|]); apply Forall_nil.
Qed.
