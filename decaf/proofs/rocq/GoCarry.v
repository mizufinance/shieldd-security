From New.code.math Require Import bits.
From New.golang.theory Require Import auto.
From Stdlib Require Import ZArith Lia.
Require Import GoCarryArithmetic.
Open Scope Z_scope.

Section carry.
Context `{ffi_sem : ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}.

Lemma addcarry_execution (x y c : w64) :
  {{{ True }}}
    bits.Add64ⁱᵐᵖˡ #x #y #c
  {{{ RET (#(word.add (word.add x y) c),
           #(word.sru (word.or (word.and x y)
             (word.and (word.or x y) (word.not (word.add (word.add x y) c)))) (W64 63)));
      True }}}.
Proof.
  pose proof (go.tagged_steps internal).
  wp_start. wp_auto. wp_end.
Qed.

Lemma addcarry_correct (x y c : w64) :
  word.unsigned c <= 1 ->
  {{{ True }}}
    bits.Add64ⁱᵐᵖˡ #x #y #c
  {{{ (lo hi : w64), RET (#lo, #hi);
      ⌜(word.unsigned lo + 2^64 * word.unsigned hi =
         word.unsigned x + word.unsigned y + word.unsigned c /\
       0 <= word.unsigned lo < 2^64 /\
       0 <= word.unsigned hi <= 1)%Z⌝ }}}.
Proof.
  intros Hc. iIntros (Φ) "_ HΦ".
  wp_apply (addcarry_execution with "[]").
  iApply "HΦ". iPureIntro.
  pose proof (addcarry_words x y c Hc) as [L H].
  rewrite L H.
  pose proof (word.unsigned_range x).
  pose proof (word.unsigned_range y).
  pose proof (word.unsigned_range c).
  pose proof (Z.div_mod (word.unsigned x + word.unsigned y + word.unsigned c)
    (2^64) ltac:(lia)).
  pose proof (Z.mod_pos_bound (word.unsigned x + word.unsigned y + word.unsigned c)
    (2^64) ltac:(lia)).
  assert (0 <= (word.unsigned x + word.unsigned y + word.unsigned c) / 2^64 < 2).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  lia.
Qed.
End carry.
