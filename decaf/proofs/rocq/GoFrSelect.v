From New.code.mizufinance_local.decaf Require Import fiat.
From New.golang.theory Require Import auto.
From Stdlib Require Import ZArith Lia.
From coqutil.Word Require Import Properties.
Open Scope Z_scope.
Section select.
Context `{ffi_sem : ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}
  `{!fiat.FrUint1_Assumptions}.

Lemma select_execution out (old c x y : w64) :
  {{{ out ↦ old }}}
    fiat.FrCmovznzU64ⁱᵐᵖˡ #out #c #x #y
  {{{ RET #(); out ↦ word.or (word.and (word.mul c (W64 (2^64-1))) y)
    (word.and (word.not (word.mul c (W64 (2^64-1)))) x) }}}.
Proof.
  pose proof (go.tagged_steps internal).
  wp_start as "Hout". wp_auto. wp_end.
Qed.
Lemma select_correct out (old c x y : w64) :
  word.unsigned c <= 1 ->
  {{{ out ↦ old }}}
    fiat.FrCmovznzU64ⁱᵐᵖˡ #out #c #x #y
  {{{ RET #(); out ↦ (if decide (word.unsigned c = 0) then x else y) }}}.
Proof.
  intros Hc. iIntros (Φ) "Hout HΦ".
  wp_apply (select_execution with "Hout"). iIntros "Hout".
  assert (c = W64 0 \/ c = W64 1) as Hbit by word.
  destruct Hbit as [Hbit|Hbit]; subst c.
  all: iApply "HΦ"; iExactEq "Hout"; f_equal.
  - change (word.or (word.and (W64 0) y) (word.and (W64 (-1)) x) = x).
    rewrite (word.and_comm _ y) word.and_0_r word.and_comm word.and_m1_r word.or_0_l. reflexivity.
  - change (word.or (word.and (W64 (-1)) y) (word.and (W64 0) x) = y).
    rewrite (word.and_comm _ y) word.and_m1_r word.and_comm word.and_0_r word.or_0_r. reflexivity.
Qed.
End select.
