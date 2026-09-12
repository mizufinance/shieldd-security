From Stdlib Require Import ZArith Lia.
From Perennial.Helpers Require Import Integers.
From coqutil.Word Require Import Properties.
Require Import GoCarryArithmetic BorrowArithmetic.
Open Scope Z_scope.

Lemma unsigned_not_and (x y : w64) :
  word.unsigned (word.and (word.not x) y) =
  Z.land (Z.lnot (word.unsigned x)) (word.unsigned y).
Proof. rewrite word.and_comm, unsigned_andnot, Z.land_comm. reflexivity. Qed.

Lemma subborrow_words (x y c : w64) :
  word.unsigned c <= 1 ->
  let difference := word.unsigned x - word.unsigned y - word.unsigned c in
  word.unsigned (word.sub (word.sub x y) c) = difference mod 2^64 /\
  word.unsigned (word.sru (word.or (word.and (word.not x) y)
    (word.and (word.not (word.xor x y)) (word.sub (word.sub x y) c))) (W64 63)) =
    -(difference / 2^64).
Proof.
  intros Hc. cbn zeta.
  assert (Difference : word.unsigned (word.sub (word.sub x y) c) =
    (word.unsigned x - word.unsigned y - word.unsigned c) mod 2^64).
  { rewrite !word.unsigned_sub. unfold word.wrap.
    rewrite Zminus_mod_idemp_l. reflexivity. }
  split; [exact Difference|].
  rewrite word.unsigned_sru_nowrap by reflexivity.
  change (word.unsigned (W64 63)) with 63.
  rewrite word.unsigned_or_nowrap, !unsigned_not_and,
    word.unsigned_xor_nowrap, Difference.
  apply borrow_bit; pose proof (word.unsigned_range x);
    pose proof (word.unsigned_range y); pose proof (word.unsigned_range c); lia.
Qed.
