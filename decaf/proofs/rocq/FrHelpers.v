From Stdlib Require Import ZArith Lia List.
From Core Require Import Core Carry RustMultiply RustBorrow RustSelect RustMultiplyRow.
From Slice Require Import Decaf_proof_slice_Fiat NativeMultiplyPrefix.
From FrSlice Require Import Decaf_fr_slice_Fiat.
Require Import FrPrefix.
Import ListNotations.
Open Scope Z_scope.
Lemma fr_multiply_same : fr_mulx_u32 = fq_mulx_u32.
Proof. reflexivity. Qed.
Print Assumptions fr_multiply_same.
Lemma fr_carry_same : fr_addcarryx_u32 = fq_addcarryx_u32.
Proof. reflexivity. Qed.
Print Assumptions fr_carry_same.
Lemma fr_borrow_same : fr_subborrowx_u32 = fq_subborrowx_u32.
Proof. reflexivity. Qed.
Print Assumptions fr_borrow_same.
Lemma fr_select_same : fr_cmovznz_u32 = fq_cmovznz_u32.
Proof. reflexivity. Qed.
Print Assumptions fr_select_same.
Lemma fr_first_row_same a b : fr_native_first_row a b = native_first_row a b.
Proof.
 unfold fr_native_first_row, native_first_row.
 rewrite !fr_multiply_same, !fr_carry_same. reflexivity.
Qed.
Lemma fr_first_row_decomposition out a b :
 fr_mul out a b = fr_native_remainder out a b (fr_native_first_row a b).
Proof.
 unfold fr_mul, fr_native_remainder, fr_native_first_row.
 do 8 (match goal with |- context[fr_mulx_u32 ?o1 ?o2 ?x ?y] =>
  destruct (fr_mulx_u32 o1 o2 x y); cbn beta iota zeta end).
 do 7 (match goal with |- context[fr_addcarryx_u32 ?o1 ?o2 ?c ?x ?y] =>
  destruct (fr_addcarryx_u32 o1 o2 c x y); cbn beta iota zeta end).
 reflexivity.
Qed.
Print Assumptions fr_first_row_same.
Print Assumptions fr_first_row_decomposition.
