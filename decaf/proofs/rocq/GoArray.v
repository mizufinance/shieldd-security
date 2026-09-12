From New.golang.theory Require Import auto array.
From Perennial.goose_lang Require Import lifting.
From Perennial.Helpers Require Import Transitions.
From Stdlib Require Import ZArith Lia List.
Open Scope Z_scope.

Lemma offset_base l i : addr_base (go.array_offset l i) = addr_base l.
Proof.
  rewrite /go.array_offset. destruct (decide (addr_base l = null)); first done.
  apply addr_base_of_plus.
Qed.

Lemma offset_zero l : go.array_offset l 0 = l.
Proof. rewrite /go.array_offset. destruct (decide (addr_base l = null)); auto using loc_add_0. Qed.

Lemma offset_add l i j : go.array_offset l (i+j) = go.array_offset (go.array_offset l i) j.
Proof.
  rewrite /go.array_offset. destruct (decide (addr_base l = null)) as [E|N].
  - rewrite decide_True; done.
  - rewrite addr_base_of_plus. rewrite decide_False; last done.
    symmetry. apply loc_add_assoc.
Qed.

Lemma offset_null_inv l i : go.array_offset l i = null -> l = null.
Proof.
  rewrite /go.array_offset. destruct (decide (addr_base l = null)) as [E|N]; first done.
  intros H. apply (f_equal addr_base) in H. rewrite addr_base_of_plus in H. contradiction.
Qed.

Ltac array_steps :=
  repeat first [progress wp_auto |
                progress (rewrite decide_False; last congruence) |
                progress (rewrite decide_True; last lia)].

Section arrays.
Context `{ffi_sem : ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}.

Lemma allocation_returns vs σ g κ e σ' g' efs :
  base_step (AllocArray (Val (ArrayV vs))) σ g κ e σ' g' efs ->
  exists l, e = Val #l /\ efs = [] /\
    isFresh (σ,g) l /\ σ' = state_init_heap_array l vs σ.
Proof.
  destruct vs; intros Hstep; rewrite /base_step /= in Hstep; monad_inv; eauto.
Qed.

Lemma allocation_progress v vs σ g :
  base_reducible (AllocArray (Val (ArrayV (v :: vs)))) σ g.
Proof.
  do 8 eexists.
  { apply fresh_locs_isFresh. }
  all: repeat eexists.
Qed.

Lemma allocate_uint64_array n (a : array.t w64 n) :
  Z.of_nat (length (array.arr a)) = n -> 0 < n ->
  {{{ True }}}
    GoAlloc (go.ArrayType n go.uint64) #a
  {{{ l, RET #l; l ↦ a }}}.
Proof.
  intros Hlen Hpos. pose proof (go.tagged_steps internal).
  pose proof (go.alloc_uint64_array n a Hlen Hpos).
  iIntros (Φ) "_ HΦ". wp_pures.
  wp_apply wp_alloc_array.
  { intros E. apply (f_equal (@length val)) in E. rewrite length_fmap in E. simpl in E. lia. }
  iIntros (l) "[[%Hnull %Hoff] [Hsize Ha]]".
  iApply "HΦ".
  rewrite typed_pointsto_unseal_eq /=.
  iSplitL; last done. iSplitR; first done.
  rewrite /pointsto_vals_toks big_sepL_fmap.
  iApply (big_sepL_mono with "Ha"). iIntros (i v Hi) "[Hv _]".
  rewrite go.array_index_ref_uint64 /go.array_offset.
  rewrite decide_False; last exact (addr_base_non_null_offset l Hnull Hoff).
  rewrite typed_pointsto_unseal_eq /=.
  iDestruct (heap_pointsto_non_null with "Hv") as %Hnonnull.
  iFrame. done.
Qed.
Lemma load_four l dq (a b c d : w64) :
  {{{ l ↦{dq} array.mk 4 [a;b;c;d] }}}
    ![go.ArrayType 4 go.uint64] #l
  {{{ RET #(array.mk 4 [a;b;c;d]); l ↦{dq} array.mk 4 [a;b;c;d] }}}.
Proof.
  pose proof (go.tagged_steps internal).
  iIntros (Φ) "Ha HΦ".
  rewrite typed_pointsto_unseal_eq /=.
  iDestruct "Ha" as "[[_ [Ha [Hb [Hc [Hd _]]]]] %Hnull]".
  array_steps.
  iApply "HΦ". iFrame. done.
Qed.

Lemma store_four l (a b c d e f g h : w64) :
  {{{ l ↦ array.mk 4 [a;b;c;d] }}}
    GoStore (go.ArrayType 4 go.uint64) (#l, #(array.mk 4 [e;f;g;h]))%V
  {{{ RET #(); l ↦ array.mk 4 [e;f;g;h] }}}.
Proof.
  pose proof (go.tagged_steps internal).
  iIntros (Φ) "Ha HΦ".
  rewrite typed_pointsto_unseal_eq /=.
  iDestruct "Ha" as "[[_ [Ha [Hb [Hc [Hd _]]]]] %Hnull]".
  array_steps. iApply "HΦ". iApply typed_pointsto_combine; first done. simpl.
  replace (word.signed (W64 (0%nat + 0))) with 0 by word.
  replace (word.signed (W64 (1%nat + 0))) with 1 by word.
  replace (word.signed (W64 (2%nat + 0))) with 2 by word.
  replace (word.signed (W64 (3%nat + 0))) with 3 by word.
  iFrame. done.
Qed.

Lemma nil_index_panics (i : w64) :
  0 <= sint.Z i < 4 ->
  ⟦IndexRef (go.ArrayType 4 go.uint64), (#null, #i)⟧ ⤳[under]
    Panic "nil array pointer".
Proof.
  intros Hi. pose proof (go.index_ref_array 4 go.uint64 i null) as Hstep.
  rewrite decide_True in Hstep; last lia.
  exact Hstep.
Qed.

Lemma invalid_index_panics (l : loc) (i : w64) :
  ~(0 <= sint.Z i < 4) ->
  ⟦IndexRef (go.ArrayType 4 go.uint64), (#l, #i)⟧ ⤳[under]
    Panic "index out of range".
Proof.
  intros Hi. pose proof (go.index_ref_array 4 go.uint64 i l) as Hstep.
  rewrite decide_False in Hstep; last done. exact Hstep.
Qed.

End arrays.
