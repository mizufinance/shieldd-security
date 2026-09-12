From Stdlib Require Import ZArith Lia.
From Perennial.Helpers Require Import Integers.
From coqutil.Word Require Import Properties.
Require Import MultiplyArithmetic.
Open Scope Z_scope.

Definition product_words (x y : w64) : w64 * w64 :=
  let x0 := word.and x (W64 (2^32-1)) in
  let x1 := word.sru x (W64 32) in
  let y0 := word.and y (W64 (2^32-1)) in
  let y1 := word.sru y (W64 32) in
  let w0 := word.mul x0 y0 in
  let t := word.add (word.mul x1 y0) (word.sru w0 (W64 32)) in
  let w1 := word.add (word.and t (W64 (2^32-1))) (word.mul x0 y1) in
  (word.add (word.add (word.mul x1 y1) (word.sru t (W64 32)))
    (word.sru w1 (W64 32)), word.mul x y).

Lemma low_half x : word.unsigned (word.and x (W64 (2^32-1))) = word.unsigned x mod 2^32.
Proof.
  rewrite word.unsigned_and_nowrap.
  replace (word.unsigned (W64 (2^32-1))) with (Z.ones 32) by reflexivity.
  apply Z.land_ones. lia.
Qed.

Lemma high_half x : word.unsigned (word.sru x (W64 32)) = word.unsigned x / 2^32.
Proof.
  rewrite word.unsigned_sru_nowrap by reflexivity.
  change (word.unsigned (W64 32)) with 32.
  apply Z.shiftr_div_pow2. lia.
Qed.

Lemma multiply_words x y :
  let '(hi,lo) := product_words x y in
  word.unsigned lo = (word.unsigned x * word.unsigned y) mod 2^64 /\
  word.unsigned hi = (word.unsigned x * word.unsigned y) / 2^64.
Proof.
  pose proof (word.unsigned_range x) as X.
  pose proof (word.unsigned_range y) as Y.
  pose proof (split_product (2^32) (word.unsigned x) (word.unsigned y)
    ltac:(lia) ltac:(change (2^32*2^32) with (2^64); lia)
    ltac:(change (2^32*2^32) with (2^64); lia)) as Bounds.
  cbn zeta in Bounds. change (2^32*2^32) with (2^64) in Bounds.
  destruct Bounds as (W0 & T & W1 & Partial & H & Result).
  unfold product_words. cbn zeta. split.
  - apply word.unsigned_mul.
  - repeat rewrite high_half.
    repeat rewrite low_half.
    repeat rewrite word.unsigned_add.
    repeat rewrite word.unsigned_mul.
    repeat first [rewrite high_half | rewrite low_half |
                  rewrite word.unsigned_add | rewrite word.unsigned_mul].
    unfold word.wrap.
    assert (X0 : 0 <= word.unsigned x mod 2^32 < 2^32) by (apply Z.mod_pos_bound; lia).
    assert (Y0 : 0 <= word.unsigned y mod 2^32 < 2^32) by (apply Z.mod_pos_bound; lia).
    assert (X1 : 0 <= word.unsigned x / 2^32 < 2^32).
    { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    assert (Y1 : 0 <= word.unsigned y / 2^32 < 2^32).
    { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    assert (P10 : 0 <= (word.unsigned x / 2^32)*(word.unsigned y mod 2^32) < 2^64) by nia.
    assert (P01 : 0 <= (word.unsigned x mod 2^32)*(word.unsigned y / 2^32) < 2^64) by nia.
    assert (P11 : 0 <= (word.unsigned x / 2^32)*(word.unsigned y / 2^32) < 2^64) by nia.
    repeat match goal with
    | B : 0 <= ?z < 2^64 |- context[?z mod 2^64] => rewrite (Z.mod_small z (2^64) B)
    end.
    exact Result.
Qed.
