From New.code.mizufinance_local.decaf Require Import arrays.
From New.golang.theory Require Import auto array.
Require Import GoArray.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.
Section source.
Context `{ffi_sem : ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}.

Lemma local_correct (x : w64) :
  {{{ True }}} arrays.Localⁱᵐᵖˡ #x {{{ RET #x; True }}}.
Proof.
  pose proof (go.tagged_steps internal).
  wp_start. wp_auto.
  wp_apply allocate_uint64_array; [reflexivity | lia |].
  iIntros (l) "Ha".
  iDestruct (typed_pointsto_not_null with "Ha") as %Hnull.
  iDestruct (array_acc l 1 _ _ _ (W64 0) with "Ha") as "[H1 Hrest]".
  { lia. }
  { reflexivity. }
  array_steps. wp_end.
Qed.
Lemma read_write_correct l (a : array.t w64 4) (i x : w64) :
  0 <= sint.Z i < 4 ->
  {{{ l ↦ a }}} arrays.ReadWriteⁱᵐᵖˡ #l #i #x
  {{{ RET #x; l ↦ array.mk 4 (<[sint.nat i := x]> (array.arr a)) }}}.
Proof.
  intros Hi. destruct a as [vs]. pose proof (go.tagged_steps internal).
  wp_start as "Ha".
  iDestruct (typed_pointsto_not_null with "Ha") as %Hnull.
  iDestruct (array_len with "Ha") as %Hlen.
  destruct (list_lookup_lt vs (sint.nat i)) as [old Hold]; first word.
  iDestruct (array_acc l (sint.Z i) _ _ _ old with "Ha") as "[Hi Hrest]".
  { lia. }
  { exact Hold. }
  array_steps. iApply "HΦ". iApply ("Hrest" with "Hi").
Qed.

Lemma copy_correct dst src (a b c d e f g h : w64) :
  {{{ dst ↦ array.mk 4 [e;f;g;h] ∗ src ↦ array.mk 4 [a;b;c;d] }}}
    arrays.Copyⁱᵐᵖˡ #dst #src
  {{{ RET #(); dst ↦ array.mk 4 [a;b;c;d] ∗ src ↦ array.mk 4 [a;b;c;d] }}}.
Proof.
  pose proof (go.tagged_steps internal).
  wp_start as "[Hdst Hsrc]".
  iEval (rewrite typed_pointsto_unseal_eq /=) in "Hdst".
  iEval (rewrite typed_pointsto_unseal_eq /=) in "Hsrc".
  iDestruct "Hdst" as "[[_ [He [Hf [Hg [Hh _]]]]] %Hdst]".
  iDestruct "Hsrc" as "[[_ [Ha [Hb [Hc [Hd _]]]]] %Hsrc]".
  array_steps. iApply "HΦ".
  repeat first [progress (replace (word.signed (W64 (0%nat + 0))) with 0 by word) |
                progress (replace (word.signed (W64 (1%nat + 0))) with 1 by word) |
                progress (replace (word.signed (W64 (2%nat + 0))) with 2 by word) |
                progress (replace (word.signed (W64 (3%nat + 0))) with 3 by word)].
  iSplitL "He Hf Hg Hh"; iApply typed_pointsto_combine; try done; simpl; iFrame; done.
Qed.

Lemma copy_same_correct l (a b c d : w64) :
  {{{ l ↦ array.mk 4 [a;b;c;d] }}}
    arrays.Copyⁱᵐᵖˡ #l #l
  {{{ RET #(); l ↦ array.mk 4 [a;b;c;d] }}}.
Proof.
  pose proof (go.tagged_steps internal).
  wp_start as "Ha".
  rewrite typed_pointsto_unseal_eq /=.
  iDestruct "Ha" as "[[_ [Ha [Hb [Hc [Hd _]]]]] %Hnull]".
  array_steps. iApply "HΦ".
  replace (word.signed (W64 (0%nat + 0))) with 0 by word.
  replace (word.signed (W64 (1%nat + 0))) with 1 by word.
  replace (word.signed (W64 (2%nat + 0))) with 2 by word.
  replace (word.signed (W64 (3%nat + 0))) with 3 by word.
  iFrame. done.
Qed.

Lemma alias_same_correct l (a b c d : w64) :
  {{{ l ↦ array.mk 4 [a;b;c;d] }}}
    arrays.Aliasⁱᵐᵖˡ #l #l
  {{{ RET #(W64 9); l ↦ array.mk 4 [a;W64 9;c;d] }}}.
Proof.
  pose proof (go.tagged_steps internal).
  wp_start as "Ha".
  iDestruct (typed_pointsto_not_null with "Ha") as %Hnull.
  iDestruct (array_acc l 1 _ _ _ b with "Ha") as "[H1 Hrest]"; [lia|reflexivity|].
  array_steps. iApply "HΦ". iApply ("Hrest" with "H1").
Qed.

End source.
