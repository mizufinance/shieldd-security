From Perennial.goose_lang Require Import lifting.
From iris.proofmode Require Import proofmode.
From Stdlib Require Import ZArith Lia List.
Require Import GoFieldEncoding.

Section memory.
Context {ext : ffi_syntax} `{hG : na_heapGS loc val Σ}.

Definition word_address l i := loc_add l (Z.of_nat i).
Lemma address_one : word_address (Loc 1 0) 1 = Loc 1 1.
Proof. reflexivity. Qed.

(* Explicit literal ownership, with no GoGlobalContext or PreSemantics. *)
Definition word_array (l : loc) dq (xs : list w64) : iProp Σ :=
  [∗ list] i ↦ x ∈ xs, heap_pointsto (word_address l i) dq (encode Uint64 x).

Lemma word_array_append l dq xs ys :
  word_array l dq (xs ++ ys) ⊣⊢
  word_array l dq xs ∗ word_array (loc_add l (Z.of_nat (List.length xs))) dq ys.
Proof.
  rewrite /word_array /word_address big_sepL_app.
  setoid_rewrite Nat2Z.inj_add. setoid_rewrite loc_add_assoc. reflexivity.
Qed.

Lemma word_array_window l dq pre mid post :
  word_array l dq (pre ++ mid ++ post) -∗
  word_array (loc_add l (Z.of_nat (List.length pre))) dq mid ∗
  (∀ replacement, ⌜List.length replacement = List.length mid⌝ -∗
    word_array (loc_add l (Z.of_nat (List.length pre))) dq replacement -∗
    word_array l dq (pre ++ replacement ++ post)).
Proof.
  iIntros "H". iDestruct (word_array_append with "H") as "[Hpre Htail]".
  iDestruct (word_array_append with "Htail") as "[Hmid Hpost]".
  iFrame "Hmid". iIntros (replacement Hlen) "Hr".
  iApply word_array_append. iFrame "Hpre".
  iApply word_array_append. iFrame "Hr". now rewrite Hlen.
Qed.

Lemma word_array_element l dq xs i x : xs !! i = Some x ->
  word_array l dq xs -∗ heap_pointsto (word_address l i) dq (encode Uint64 x) ∗
  (∀ y, heap_pointsto (word_address l i) dq (encode Uint64 y) -∗
    word_array l dq (<[i := y]> xs)).
Proof.
  intros Hlookup. rewrite /word_array. iIntros "H".
  iDestruct (big_sepL_insert_acc _ _ i with "H") as "[Hx Hr]"; first exact Hlookup.
  iFrame "Hx". iIntros (y) "Hy". iApply "Hr". iExact "Hy".
Qed.

(* The native array wrapper carries a dynamic list-length invariant. *)
Lemma native_four_view (a : array.t w64 4) : List.length (array.arr a) = 4%nat ->
  wellformed (Array 4 Uint64) (array.arr a).
Proof.
  intros Hlen. split; first exact Hlen.
  apply List.Forall_forall. intros x Hx. exact I.
Qed.

End memory.
