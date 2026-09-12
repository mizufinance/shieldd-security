From New.code.math Require Import bits.
From New.golang.theory Require Import auto.
From Stdlib Require Import ZArith Lia.
Require Import GoBorrowArithmetic.
Open Scope Z_scope.

Section borrow.
Context `{ffi_sem : ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}.

Lemma subborrow_execution (x y c : w64) :
  {{{ True }}}
    bits.Sub64ⁱᵐᵖˡ #x #y #c
  {{{ RET (#(word.sub (word.sub x y) c),
           #(word.sru (word.or (word.and (word.not x) y)
             (word.and (word.not (word.xor x y)) (word.sub (word.sub x y) c))) (W64 63)));
      True }}}.
Proof.
  pose proof (go.tagged_steps internal).
  wp_start. wp_auto. wp_end.
Qed.

Lemma subborrow_correct (x y c : w64) :
  word.unsigned c <= 1 ->
  {{{ True }}}
    bits.Sub64ⁱᵐᵖˡ #x #y #c
  {{{ (lo hi : w64), RET (#lo, #hi);
      ⌜(word.unsigned lo - 2^64 * word.unsigned hi =
         word.unsigned x - word.unsigned y - word.unsigned c /\
       0 <= word.unsigned lo < 2^64 /\
       0 <= word.unsigned hi <= 1)%Z⌝ }}}.
Proof.
  intros Hc. iIntros (Φ) "_ HΦ".
  wp_apply (subborrow_execution with "[]").
  iApply "HΦ". iPureIntro.
  pose proof (subborrow_words x y c Hc) as [L H].
  rewrite L H.
  pose proof (word.unsigned_range x).
  pose proof (word.unsigned_range y).
  pose proof (word.unsigned_range c).
  pose proof (Z.div_mod (word.unsigned x - word.unsigned y - word.unsigned c)
    (2^64) ltac:(lia)).
  pose proof (Z.mod_pos_bound (word.unsigned x - word.unsigned y - word.unsigned c)
    (2^64) ltac:(lia)).
  assert (-1 <= (word.unsigned x - word.unsigned y - word.unsigned c) / 2^64 < 1).
  { split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]. }
  lia.
Qed.
End borrow.
