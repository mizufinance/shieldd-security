From Stdlib Require Import ZArith Lia List.
Require Import FiatMultiply MontgomeryBridge.
Global Opaque RustFq.body RustFq.correct.
Module AM := Crypto.Arithmetic.WordByWordMontgomery.WordByWordMontgomery.
Module PB := Crypto.PushButtonSynthesis.WordByWordMontgomery.
Open Scope Z_scope.
Definition inv_word : Z := 8444461747462240959818935500049758586515714180585683306521814100294163660801.
Definition decoded (v : list Z) := @AM.eval 32 8 (AM.from_montgomerymod 32 8 fq (PB.m' fq 32) v).
Lemma decode_correct v : AM.valid 32 8 fq v ->
 decoded v mod fq = (@AM.eval 32 8 v * inv_word^8) mod fq.
Proof.
  unfold decoded. apply (AM.eval_from_montgomerymod 32 8 fq inv_word (PB.m' fq 32)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - lia.
  - unfold fq; lia.
  - discriminate.
  - unfold fq; vm_compute; reflexivity.
Qed.
Definition fiat_mul := Language.Compilers.expr.Interp (@IdentifiersBasicGENERATED.Compilers.ident_interp) RustFq.body.
Theorem fiat_decoded_product a b : AM.valid 32 8 fq a -> AM.valid 32 8 fq b ->
 let result := fiat_mul a b in
 AM.valid 32 8 fq result /\
 (@AM.eval 32 8 result * inv_word^8) mod fq =
 (@AM.eval 32 8 a * @AM.eval 32 8 b * inv_word^8 * inv_word^8) mod fq.
Proof.
  intros Ha Hb.
  destruct (RustFq.correct a b Ha Hb) as [Hmul Hvalid].
  change (decoded (fiat_mul a b) mod fq = (decoded a * decoded b) mod fq) in Hmul.
  change (AM.valid 32 8 fq (fiat_mul a b)) in Hvalid.
  split; [exact Hvalid|].
  rewrite (decode_correct _ Hvalid) in Hmul.
  rewrite (Z.mul_mod (decoded a) (decoded b) fq) in Hmul by (unfold fq; lia).
  rewrite (decode_correct a Ha), (decode_correct b Hb) in Hmul.
  rewrite <- Z.mul_mod in Hmul by (unfold fq; lia).
  replace (@AM.eval 32 8 a * inv_word^8 * (@AM.eval 32 8 b * inv_word^8))
    with (@AM.eval 32 8 a * @AM.eval 32 8 b * inv_word^8 * inv_word^8) in Hmul by ring.
  exact Hmul.
Qed.


