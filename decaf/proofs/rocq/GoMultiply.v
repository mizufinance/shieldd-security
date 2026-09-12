From New.code.math Require Import bits.
From New.golang.theory Require Import auto.
From Stdlib Require Import ZArith Lia.
Require Import GoMultiplyArithmetic.
Open Scope Z_scope.

Section multiply.
Context `{ffi_sem : ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}.

Lemma multiply_execution (x y : w64) :
  {{{ True }}}
    bits.Mul64ⁱᵐᵖˡ #x #y
  {{{ RET (#(fst (product_words x y)), #(snd (product_words x y))); True }}}.
Proof.
  pose proof (go.tagged_steps internal).
  wp_start. wp_auto. wp_end.
Qed.

Lemma multiply_correct (x y : w64) :
  {{{ True }}}
    bits.Mul64ⁱᵐᵖˡ #x #y
  {{{ (hi lo : w64), RET (#hi, #lo);
      ⌜(word.unsigned lo + 2^64 * word.unsigned hi =
         word.unsigned x * word.unsigned y /\
       0 <= word.unsigned lo < 2^64 /\
       0 <= word.unsigned hi < 2^64)%Z⌝ }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_apply (multiply_execution with "[]").
  iApply "HΦ". iPureIntro.
  pose proof (multiply_words x y) as H.
  destruct (product_words x y) as [hi lo]. cbn in *.
  destruct H as [L H].
  pose proof (word.unsigned_range hi).
  pose proof (word.unsigned_range lo).
  split; [|lia]. rewrite L H.
  pose proof (Z.div_mod (word.unsigned x * word.unsigned y) (2^64) ltac:(lia)). lia.
Qed.
End multiply.
