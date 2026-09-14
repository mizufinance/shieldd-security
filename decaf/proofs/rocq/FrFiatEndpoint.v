From Stdlib Require Import ZArith Lia List.
Require Import FiatMultiply MontgomeryBridge.
Global Opaque RustFr.body RustFr.correct.
Module AM := Crypto.Arithmetic.WordByWordMontgomery.WordByWordMontgomery.
Module PB := Crypto.PushButtonSynthesis.WordByWordMontgomery.
Open Scope Z_scope.
Definition inv_word : Z := 930952801561512890121205999574895092486256886683201982265257124862830430685.
Definition decoded (v : list Z) := @AM.eval 32 8 (AM.from_montgomerymod 32 8 fr (PB.m' fr 32) v).
Lemma decode_correct v : AM.valid 32 8 fr v ->
 decoded v mod fr = (@AM.eval 32 8 v * inv_word^8) mod fr.
Proof.
  unfold decoded. apply (AM.eval_from_montgomerymod 32 8 fr inv_word (PB.m' fr 32)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - lia.
  - unfold fr; lia.
  - discriminate.
  - unfold fr; vm_compute; reflexivity.
Qed.
Definition fiat_mul := Language.Compilers.expr.Interp (@IdentifiersBasicGENERATED.Compilers.ident_interp) RustFr.body.
Theorem fiat_decoded_product a b : AM.valid 32 8 fr a -> AM.valid 32 8 fr b ->
 let result := fiat_mul a b in
 AM.valid 32 8 fr result /\
 (@AM.eval 32 8 result * inv_word^8) mod fr =
 (@AM.eval 32 8 a * @AM.eval 32 8 b * inv_word^8 * inv_word^8) mod fr.
Proof.
  intros Ha Hb.
  destruct (RustFr.correct a b Ha Hb) as [Hmul Hvalid].
  change (decoded (fiat_mul a b) mod fr = (decoded a * decoded b) mod fr) in Hmul.
  change (AM.valid 32 8 fr (fiat_mul a b)) in Hvalid.
  split; [exact Hvalid|].
  rewrite (decode_correct _ Hvalid) in Hmul.
  rewrite (Z.mul_mod (decoded a) (decoded b) fr) in Hmul by (unfold fr; lia).
  rewrite (decode_correct a Ha), (decode_correct b Hb) in Hmul.
  rewrite <- Z.mul_mod in Hmul by (unfold fr; lia).
  replace (@AM.eval 32 8 a * inv_word^8 * (@AM.eval 32 8 b * inv_word^8))
    with (@AM.eval 32 8 a * @AM.eval 32 8 b * inv_word^8 * inv_word^8) in Hmul by ring.
  exact Hmul.
Qed.


