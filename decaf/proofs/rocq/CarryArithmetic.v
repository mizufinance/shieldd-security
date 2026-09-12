From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma carry_bit x y c :
  0 <= x < 2^64 -> 0 <= y < 2^64 -> 0 <= c <= 1 ->
  Z.shiftr (Z.lor (Z.land x y)
    (Z.land (Z.lor x y) (Z.lnot ((x+y+c) mod 2^64)))) 63 =
  (x+y+c) / 2^64.
Proof.
  intros Hx Hy Hc.
  rewrite Z.shiftr_lor, !Z.shiftr_land, Z.shiftr_lor.
  rewrite <- Z.lnot_shiftr by lia.
  rewrite !Z.shiftr_div_pow2 by lia.
  assert (X : x / 2^63 = 0 \/ x / 2^63 = 1).
  { assert (0 <= x / 2^63 < 2).
    { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    lia. }
  assert (Y : y / 2^63 = 0 \/ y / 2^63 = 1).
  { assert (0 <= y / 2^63 < 2).
    { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    lia. }
  pose proof (Z.div_mod x (2^63) ltac:(lia)) as Ex.
  pose proof (Z.div_mod y (2^63) ltac:(lia)) as Ey.
  pose proof (Z.mod_pos_bound x (2^63) ltac:(lia)) as Rx.
  pose proof (Z.mod_pos_bound y (2^63) ltac:(lia)) as Ry.
  destruct X as [X|X]; destruct Y as [Y|Y]; rewrite X, Y in *.
  all: destruct (Z_lt_ge_dec (x+y+c) (2^64)) as [Hs|Hs].
  all: try (rewrite (Z.div_small (x+y+c) (2^64)) by lia).
  all: try (assert (Q : (x+y+c) / 2^64 = 1) by
    (symmetry; apply Z.div_unique with (r := x+y+c-2^64); lia); rewrite Q).
  all: try (rewrite (Z.mod_small (x+y+c) (2^64)) by lia).
  all: try (assert (R : (x+y+c) mod 2^64 = x+y+c-2^64) by
    (symmetry; apply Z.mod_unique with (q := 1); lia); rewrite R).
  all: try (assert (H : (x+y+c) / 2^63 = 1) by
    (symmetry; apply Z.div_unique with (r := x+y+c-2^63); lia); rewrite H).
  all: try (rewrite (Z.div_small (x+y+c-2^64) (2^63)) by lia).
  all: try reflexivity; try lia.
  assert (L : 0 <= (x+y+c-2^64) / 2^63 < 2).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  assert (D : (x+y+c-2^64) / 2^63 = 0 \/
              (x+y+c-2^64) / 2^63 = 1) by lia.
  destruct D as [D|D]; rewrite D; reflexivity.
Qed.
