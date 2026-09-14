From New.golang.theory Require Import auto array.
From Stdlib Require Import ZArith Lia List.
Open Scope Z_scope.

Section windows.
Context `{ffi_sem : ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}.

Lemma array_append (l : loc) dq (xs ys : list w64) :
  l ↦{dq} array.mk (Z.of_nat (length (xs ++ ys))) (xs ++ ys) ⊣⊢
  l ↦{dq} array.mk (Z.of_nat (length xs)) xs ∗
  array_index_ref w64 (Z.of_nat (length xs)) l ↦{dq}
    array.mk (Z.of_nat (length ys)) ys.
Proof.
  rewrite typed_pointsto_unseal /typed_pointsto_wrap /typed_pointsto_def /=.
  rewrite big_sepL_app.
  setoid_rewrite Nat2Z.inj_add.
  setoid_rewrite <- go.array_index_ref_add.
  iSplit.
  - iIntros "((% & Hxs & Hys) & %Hn)".
    iSplitL "Hxs".
    + iFrame. done.
    + iFrame. iSplit; first done. iPureIntro.
      intros Hnull. apply go.array_index_ref_null_inv in Hnull. done.
  - iIntros "(((% & Hxs) & %Hn) & ((% & Hys) & %))".
    iFrame. done.
Qed.

Lemma array_window (l : loc) dq (pre mid post : list w64) :
  l ↦{dq} array.mk (Z.of_nat (length (pre ++ mid ++ post))) (pre ++ mid ++ post) -∗
  array_index_ref w64 (Z.of_nat (length pre)) l ↦{dq}
    array.mk (Z.of_nat (length mid)) mid ∗
  (∀ vs : list w64, ⌜length vs = length mid⌝ -∗
    array_index_ref w64 (Z.of_nat (length pre)) l ↦{dq}
      array.mk (Z.of_nat (length vs)) vs -∗
    l ↦{dq} array.mk (Z.of_nat (length (pre ++ vs ++ post))) (pre ++ vs ++ post)).
Proof.
  iIntros "H".
  iDestruct (array_append with "H") as "[Hpre Htail]".
  iDestruct (array_append with "Htail") as "[Hmid Hpost]".
  iFrame "Hmid". iIntros (vs Hlen) "Hvs".
  iApply array_append. iFrame "Hpre".
  iApply array_append. iFrame "Hvs".
  rewrite Hlen. iExact "Hpost".
Qed.

Lemma array_window4 (l : loc) dq (pre mid post : list w64) :
  length mid = 4%nat ->
  l ↦{dq} array.mk (Z.of_nat (length (pre ++ mid ++ post))) (pre ++ mid ++ post) -∗
  array_index_ref w64 (Z.of_nat (length pre)) l ↦{dq} array.mk 4 mid ∗
  (∀ result : array.t w64 4,
    array_index_ref w64 (Z.of_nat (length pre)) l ↦{dq} result -∗
    l ↦{dq} array.mk (Z.of_nat (length (pre ++ mid ++ post))) (pre ++ array.arr result ++ post)).
Proof.
  intros Hmid. iIntros "H".
  iDestruct (array_window with "H") as "[Hmid Hrestore]".
  rewrite Hmid. iFrame "Hmid".
  iIntros ([vs]) "Hvs".
  iDestruct (array_len with "Hvs") as %Hlen.
  assert (Hvs : length vs = 4%nat) by lia.
  iSpecialize ("Hrestore" $! vs with "[] [Hvs]").
  { done. }
  { rewrite Hvs. iExact "Hvs". }
  iExactEq "Hrestore". f_equal. f_equal. repeat rewrite length_app. rewrite Hmid Hvs. reflexivity.
Qed.

End windows.
