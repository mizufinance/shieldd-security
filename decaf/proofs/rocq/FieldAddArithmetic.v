From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(* Pure reduction arithmetic only; native execution supplies every premise. *)
Lemma reduced_add (modulus radix capacity total sum difference carry borrow top last : Z) :
  0 < modulus -> 1 < radix -> 2 * modulus < capacity ->
  0 <= total < 2 * modulus ->
  0 <= sum < capacity -> 0 <= difference < capacity ->
  0 <= carry <= 1 -> 0 <= borrow <= 1 ->
  0 <= top < radix -> 0 <= last <= 1 ->
  sum + capacity * carry = total ->
  difference - capacity * borrow = sum - modulus ->
  top - radix * last = carry - borrow ->
  let result := if Z.eq_dec last 0 then difference else sum in
  0 <= result < modulus /\ result = total mod modulus.
Proof.
  intros Hm Hr Hcap Htotal Hsum Hdiff Hcarry Hborrow Htop Hlast
    Haddition Hsubtraction Hfinal.
  assert (carry = 0) by nia.
  subst carry.
  assert (last = borrow) by nia.
  destruct (Z.eq_dec last 0) as [Hz|Hnz]; cbn zeta.
  - assert (borrow = 0) by lia. subst borrow.
    split; [nia|apply Z.mod_unique with (q := 1); nia].
  - assert (borrow = 1) by lia. subst borrow.
    split; [nia|apply Z.mod_unique with (q := 0); nia].
Qed.

Print Assumptions reduced_add.
