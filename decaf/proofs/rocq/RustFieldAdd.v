From Stdlib Require Import ZArith Lia List.
From Core Require Import Core Carry RustBorrow RustSelect RustArray.
From Slice Require Import Decaf_proof_slice_Fiat.
Import ListNotations.
Open Scope Z_scope.

Definition fq_modulus : Z :=
  8444461749428370424248824938781546531375899335154063827935233455917409239041.
Fixpoint limbs_value (xs : list t_u32) : Z :=
  match xs with [] => 0 | x::xs => U32.raw x + 4294967296 * limbs_value xs end.

Lemma cast_carry_canonical (c : t_u8) : U32.canonical (cast c : t_u32).
Proof.
  unfold U32.canonical, cast, U32.of_Z, U32.raw, F32.width.
  cbn [integer_u8 integer_u32 from_Z]. apply Z.mod_pos_bound; lia.
Qed.

Lemma cast_carry_value (c : t_u8) :
  0 <= U8.raw c <= 1 -> U32.raw (cast c : t_u32) = U8.raw c.
Proof.
  destruct c as [c]. unfold cast, U32.raw, U32.of_Z, U8.value, U8.raw.
  cbn [integer_u8 integer_u32 from_Z value F8.signed F32.width].
  unfold U32.of_Z, U8.value, U8.raw, F8.signed, F32.width. cbn.
  intros. apply Z.mod_small; lia.
Qed.

Ltac array8 xs Hlen :=
  do 8 (let x := fresh "limb" in destruct xs as [|x xs]; [cbn in Hlen; discriminate|]);
  destruct xs; [|cbn in Hlen; discriminate].

Ltac limb_bound := first [assumption | apply cast_carry_canonical |
  unfold U32.canonical, U32.raw, U32.of_Z, U8.raw, U8.of_Z, F32.width, F8.width; cbn; lia].

Ltac carry_step :=
  match goal with |- context[fq_addcarryx_u32 ?o1 ?o2 ?c ?x ?y] =>
    let H := fresh "sum_equation" in
    pose proof (addcarry_reconstruction o1 o2 c x y ltac:(limb_bound)
      ltac:(limb_bound) ltac:(limb_bound)) as H;
    let lo := fresh "sum_limb" in let hi := fresh "carry" in
    destruct (fq_addcarryx_u32 o1 o2 c x y) as [lo hi];
    cbn [fst snd] in H; destruct H as [? [? ?]]; cbn beta iota zeta
  end.

Ltac borrow_step :=
  match goal with |- context[fq_subborrowx_u32 ?o1 ?o2 ?c ?x ?y] =>
    let H := fresh "difference_equation" in
    pose proof (borrow_reconstruction o1 o2 c x y ltac:(limb_bound)
      ltac:(limb_bound) ltac:(limb_bound)) as H;
    let lo := fresh "difference_limb" in let hi := fresh "borrow" in
    destruct (fq_subborrowx_u32 o1 o2 c x y) as [lo hi];
    cbn [fst snd] in H; destruct H as [? [? ?]]; cbn beta iota zeta
  end.

Theorem add_correct out a b :
  length out = 8%nat -> length a = 8%nat -> length b = 8%nat ->
  Forall U32.canonical a -> Forall U32.canonical b ->
  0 <= limbs_value a < fq_modulus -> 0 <= limbs_value b < fq_modulus ->
  let result := fq_add out a b in
  length result = 8%nat /\ Forall U32.canonical result /\
  limbs_value result = (limbs_value a + limbs_value b) mod fq_modulus.
Proof.
  intros Ho Ha Hb Hca Hcb Hva Hvb.
  array8 out Ho. array8 a Ha. array8 b Hb.
  repeat match goal with H : Forall _ (_::_) |- _ => inversion H; subst; clear H end.
  unfold fq_add.
  cbn [f_index nth U64.value U64.raw U64.of_Z F64.width F64.signed].
  repeat carry_step.
  repeat borrow_step.
  repeat rewrite cast_carry_value in * by assumption.
  repeat rewrite select_exact by limb_bound.
  match goal with |- context[if U8.raw ?c =? 0 then _ else _] =>
    destruct (Z.eqb_spec (U8.raw c) 0)
  end.
  all: unfold update_at_usize, U64.value, U64.raw, U64.of_Z, F64.width, F64.signed in *.
  all: change (2^64) with 18446744073709551616 in *.
  all: cbn -[Z.mul] in *.
  all: change (Pos.to_nat 1) with 1%nat in *.
  all: change (Pos.to_nat 2) with 2%nat in *.
  all: change (Pos.to_nat 3) with 3%nat in *.
  all: change (Pos.to_nat 4) with 4%nat in *.
  all: change (Pos.to_nat 5) with 5%nat in *.
  all: change (Pos.to_nat 6) with 6%nat in *.
  all: change (Pos.to_nat 7) with 7%nat in *.
  all: cbn -[Z.mul] in *.
  all: split; [reflexivity|].
  all: split; [repeat (apply Forall_cons; [assumption|]); apply Forall_nil|].
  all: repeat rewrite cast_carry_value in * by assumption.
  all: unfold U32.canonical, fq_modulus in *.
  all: cbn [limbs_value] in *.
  all: unfold U32.of_Z, U8.of_Z, F32.width, F8.width in *.
  all: change (2^32) with 4294967296 in *.
  all: change (2^8) with 256 in *.
  all: cbn -[Z.mul] in *.
  - apply Z.mod_unique with (q := 1); lia.
  - apply Z.mod_unique with (q := 0); lia.
Qed.

Theorem add_accesses (out a b values : list t_u32) :
  length out = 8%nat -> length a = 8%nat -> length b = 8%nat ->
  Forall (index_defined a) indices8 /\
  Forall (index_defined b) indices8 /\
  writes_safe out (combine indices8 values).
Proof.
  intros. split; [apply indices8_safe; assumption|].
  split; [apply indices8_safe; assumption|].
  apply writes8_safe; assumption.
Qed.
