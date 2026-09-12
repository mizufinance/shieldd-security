From Stdlib Require Import ZArith Lia.
From Perennial.Helpers Require Import Integers.
From coqutil.Z Require Import bitblast.
From coqutil.Word Require Import Properties.
Require Import CarryArithmetic.
Open Scope Z_scope.

Lemma unsigned_andnot (x y : w64) :
  word.unsigned (word.and x (word.not y)) =
  Z.land (word.unsigned x) (Z.lnot (word.unsigned y)).
Proof.
  rewrite word.unsigned_and, word.unsigned_not. unfold word.wrap.
  rewrite <- (word.wrap_unsigned x), <- (word.wrap_unsigned y).
  Z.bitblast.
Qed.

Lemma addcarry_words (x y c : w64) :
  word.unsigned c <= 1 ->
  let total := word.unsigned x + word.unsigned y + word.unsigned c in
  word.unsigned (word.add (word.add x y) c) = total mod 2^64 /\
  word.unsigned (word.sru (word.or (word.and x y)
    (word.and (word.or x y) (word.not (word.add (word.add x y) c)))) (W64 63))
    = total / 2^64.
Proof.
  intros Hc. cbn zeta.
  assert (Sum : word.unsigned (word.add (word.add x y) c) =
    (word.unsigned x + word.unsigned y + word.unsigned c) mod 2^64).
  { rewrite !word.unsigned_add. unfold word.wrap.
    rewrite Z.add_mod_idemp_l by lia. reflexivity. }
  split; [exact Sum|].
  rewrite word.unsigned_sru_nowrap by reflexivity.
  change (word.unsigned (W64 63)) with 63.
  rewrite word.unsigned_or_nowrap, unsigned_andnot,
    word.unsigned_and_nowrap, word.unsigned_or_nowrap, Sum.
  apply carry_bit; pose proof (word.unsigned_range x);
    pose proof (word.unsigned_range y); pose proof (word.unsigned_range c); lia.
Qed.
