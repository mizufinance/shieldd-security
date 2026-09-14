From Perennial.goose_lang Require Import lang.
From Stdlib Require Import ZArith.

Section integer_literals.
Context {ext : ffi_syntax}.
(* An injective syntax representation for Go's unbounded untyped constants.
   The location-shaped payload is data under a sum tag, never a heap address. *)
Definition integer_literal (z : Z) : val := InjLV (LitV (LitLoc (Loc z 0))).
Definition integer_decode (v : val) : option Z :=
  match v with
  | InjLV (LitV (LitLoc (Loc z off))) => if Z.eqb off 0 then Some z else None
  | _ => None
  end.

Lemma integer_roundtrip z : integer_decode (integer_literal z) = Some z.
Proof. reflexivity. Qed.
Lemma integer_injective x y : integer_literal x = integer_literal y -> x = y.
Proof. intros H. now inversion H. Qed.
Lemma integer_sound v z : integer_decode v = Some z -> integer_literal z = v.
Proof.
  destruct v; cbn; try discriminate.
  destruct v; try discriminate. destruct l; try discriminate.
  destruct l as [value off]. cbn.
  destruct (Z.eqb off 0) eqn:Ho; try discriminate.
  apply Z.eqb_eq in Ho. intros H. inversion H; subst. reflexivity.
Qed.
End integer_literals.
