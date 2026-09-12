From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma top_bit z : 0 <= z < 2^64 -> z / 2^63 = 0 \/ z / 2^63 = 1.
Proof.
  intros Hz. assert (0 <= z / 2^63 < 2).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  lia.
Qed.

Lemma borrow_bit x y c :
  0 <= x < 2^64 -> 0 <= y < 2^64 -> 0 <= c <= 1 ->
  Z.shiftr (Z.lor (Z.land (Z.lnot x) y)
    (Z.land (Z.lnot (Z.lxor x y)) ((x-y-c) mod 2^64))) 63 =
  -((x-y-c) / 2^64).
Proof.
  intros Hx Hy Hc.
  rewrite Z.shiftr_lor, !Z.shiftr_land.
  repeat rewrite <- Z.lnot_shiftr by lia.
  rewrite Z.shiftr_lxor.
  rewrite !Z.shiftr_div_pow2 by lia.
  pose proof (top_bit x Hx) as X.
  pose proof (top_bit y Hy) as Y.
  pose proof (Z.mod_pos_bound (x-y-c) (2^64) ltac:(lia)) as Hr.
  pose proof (top_bit ((x-y-c) mod 2^64) Hr) as D.
  pose proof (Z.div_mod x (2^63) ltac:(lia)) as Ex.
  pose proof (Z.div_mod y (2^63) ltac:(lia)) as Ey.
  pose proof (Z.mod_pos_bound x (2^63) ltac:(lia)) as Rx.
  pose proof (Z.mod_pos_bound y (2^63) ltac:(lia)) as Ry.
  pose proof (Z.div_mod (x-y-c) (2^64) ltac:(lia)) as Es.
  pose proof (Z.div_mod ((x-y-c) mod 2^64) (2^63) ltac:(lia)) as Ed.
  pose proof (Z.mod_pos_bound ((x-y-c) mod 2^64) (2^63) ltac:(lia)) as Rd.
  assert (Q : (x-y-c) / 2^64 = -1 \/ (x-y-c) / 2^64 = 0).
  { assert (-1 <= (x-y-c) / 2^64 < 1).
    { split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]. }
    lia. }
  destruct X as [X|X]; destruct Y as [Y|Y]; destruct D as [D|D]; destruct Q as [Q|Q].
  all: rewrite X, Y, D, Q in *; cbn; lia.
Qed.
