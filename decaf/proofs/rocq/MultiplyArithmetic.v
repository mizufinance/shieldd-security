From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma split_product b x y :
  1 < b -> 0 <= x < b*b -> 0 <= y < b*b ->
  let x0 := x mod b in let x1 := x / b in
  let y0 := y mod b in let y1 := y / b in
  let w0 := x0*y0 in
  let t := x1*y0 + w0/b in
  let w1 := t mod b + x0*y1 in
  let hi := x1*y1 + t/b + w1/b in
  0 <= w0 < b*b /\ 0 <= t < b*b /\ 0 <= w1 < b*b /\
  0 <= x1*y1 + t/b < b*b /\ 0 <= hi < b*b /\ hi = (x*y)/(b*b).
Proof.
  intros Hb Hx Hy. cbn zeta.
  pose proof (Z.mod_pos_bound x b ltac:(lia)) as X0.
  pose proof (Z.mod_pos_bound y b ltac:(lia)) as Y0.
  assert (X1 : 0 <= x/b < b).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; nia]. }
  assert (Y1 : 0 <= y/b < b).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; nia]. }
  set (x0 := x mod b) in *; set (x1 := x/b) in *.
  set (y0 := y mod b) in *; set (y1 := y/b) in *.
  assert (P00 : 0 <= x0*y0 <= (b-1)*(b-1)) by nia.
  assert (P10 : 0 <= x1*y0 <= (b-1)*(b-1)) by nia.
  assert (P01 : 0 <= x0*y1 <= (b-1)*(b-1)) by nia.
  assert (P11 : 0 <= x1*y1 <= (b-1)*(b-1)) by nia.
  assert (W0 : 0 <= x0*y0/b < b).
  { split; [apply Z.div_pos; nia | apply Z.div_lt_upper_bound; nia]. }
  set (t := x1*y0 + x0*y0/b).
  assert (T : 0 <= t < b*b) by (unfold t; nia).
  pose proof (Z.mod_pos_bound t b ltac:(lia)) as T0.
  assert (T1 : 0 <= t/b < b).
  { split; [apply Z.div_pos; nia | apply Z.div_lt_upper_bound; nia]. }
  set (w1 := t mod b + x0*y1).
  assert (W1 : 0 <= w1 < b*b) by (unfold w1; nia).
  assert (W11 : 0 <= w1/b < b).
  { split; [apply Z.div_pos; nia | apply Z.div_lt_upper_bound; nia]. }
  assert (H : 0 <= x1*y1 + t/b + w1/b < b*b) by nia.
  repeat split; try nia.
  apply Z.div_unique with (r := (x0*y0) mod b + b*(w1 mod b)).
  - left. pose proof (Z.mod_pos_bound (x0*y0) b ltac:(lia)).
    pose proof (Z.mod_pos_bound w1 b ltac:(lia)). nia.
  - pose proof (Z.div_mod x b ltac:(lia)) as EX.
    pose proof (Z.div_mod y b ltac:(lia)) as EY.
    change (x = b*x1+x0) in EX. change (y = b*y1+y0) in EY.
    pose proof (Z.div_mod (x0*y0) b ltac:(lia)).
    pose proof (Z.div_mod t b ltac:(lia)).
    pose proof (Z.div_mod w1 b ltac:(lia)).
    clearbody x0 x1 y0 y1. unfold w1, t in *. rewrite EX, EY. nia.
Qed.
