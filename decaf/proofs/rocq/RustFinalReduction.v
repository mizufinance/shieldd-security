From Stdlib Require Import ZArith Lia List.
From Core Require Import Core Carry RustBorrow RustSelect RustArray RustMultiply RustFiatPrimitives RustFieldAdd RustMultiplyWords RustMultiplyRow RustFirstReduction RustMultiplyRound.
From Slice Require Import Decaf_proof_slice_Fiat NativeMultiplyPrefix.
From Slice Require Import NativeSuffixDefinition8.
Import ListNotations.
Open Scope Z_scope.
Theorem final_correct out acc : length out = 8%nat -> length acc = 9%nat ->
  Forall U32.canonical acc -> 0 <= limbs_value acc < 2 * fq_modulus ->
  let result := native_final out acc in
  length result = 8%nat /\ Forall U32.canonical result /\
  limbs_value result = limbs_value acc mod fq_modulus.
Proof.
  intros Ho Ha Hca Hva.
  pose proof (nine_words_top_zero acc Ha Hca Hva) as Htop.
  array8 out Ho. array9 acc Ha.
  repeat match goal with H : Forall _ (_::_) |- _ => inversion H; subst; clear H end.
  cbn [nth] in Htop.
  unfold native_final.
  repeat borrow_step.
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
  all: unfold U32.canonical, fq_modulus in *.
  all: cbn [limbs_value] in *.
  all: unfold U32.of_Z, U8.of_Z, F32.width, F8.width in *.
  all: change (2^32) with 4294967296 in *.
  all: change (2^8) with 256 in *.
  all: cbn -[Z.mul] in *.
  - apply Z.mod_unique with (q := 1); lia.
  - apply Z.mod_unique with (q := 0); lia.
Qed.
Print Assumptions final_correct.

Theorem final_state_independent out other acc :
  length out = 8%nat -> length other = 8%nat -> length acc = 9%nat ->
  native_final out acc = native_final other acc.
Proof.
  intros Ho Hother Ha. array8 out Ho. array8 other Hother. array9 acc Ha.
  unfold native_final.
  do 9 (match goal with |- context[fq_subborrowx_u32 ?o1 ?o2 ?c ?x ?y] =>
    destruct (fq_subborrowx_u32 o1 o2 c x y); cbn beta iota zeta end).
  reflexivity.
Qed.
Print Assumptions final_state_independent.
