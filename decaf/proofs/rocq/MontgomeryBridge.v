From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.
Lemma congruence_witness q x y : q <> 0 -> x mod q = y mod q ->
  exists k, x = y + q*k.
Proof.
  intros Hq Hmod.
  pose proof (Z.div_mod x q Hq) as Hx.
  pose proof (Z.div_mod y q Hq) as Hy.
  exists (x/q-y/q). nia.
Qed.
Lemma congruence_from_witness q x y k : q <> 0 -> x = y + q*k -> x mod q = y mod q.
Proof.
  intros Hq H. rewrite H. replace (q*k) with (k*q) by ring.
  rewrite Z.mod_add by assumption. reflexivity.
Qed.
Theorem native_decoded_product q R S t x a b k :
  q <> 0 -> R*S = 1+q*t -> R*x=a*b+q*k ->
  (x*S) mod q = (a*b*S*S) mod q.
Proof.
  intros Hq Hunit Hnative.
  apply congruence_from_witness with (k := k*S*S-x*S*t); [exact Hq|].
  assert (Hscaled : R*x*S*S = (a*b+q*k)*S*S) by now rewrite Hnative.
  replace (R*x*S*S) with (x*S*(R*S)) in Hscaled by ring.
  rewrite Hunit in Hscaled. nia.
Qed.
Theorem cancel_decoding q R S t x y :
  q <> 0 -> R*S=1+q*t -> (x*S) mod q=(y*S) mod q -> x mod q=y mod q.
Proof.
  intros Hq Hunit Hmod.
  destruct (congruence_witness q (x*S) (y*S) Hq Hmod) as [k Hk].
  apply congruence_from_witness with (k := k*R-(x-y)*t); [exact Hq|].
  pose proof (f_equal (fun z => z*R) Hk) as Hscaled. cbn beta in Hscaled.
  replace (x*S*R) with (x*(R*S)) in Hscaled by ring.
  replace ((y*S+q*k)*R) with (y*(R*S)+q*k*R) in Hscaled by ring.
  rewrite Hunit in Hscaled. nia.
Qed.
Print Assumptions native_decoded_product.
Print Assumptions cancel_decoding.

