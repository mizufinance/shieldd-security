From New.golang.theory Require Import auto array.
Section model.
Context `{ffi_sem : ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}.
Lemma contradictory_array_addresses : False.
Proof.
  pose proof (go.array_index_ref_null_inv w8 (-1) (Loc 0 1)) as H.
  rewrite go.array_index_ref_add_loc_add in H.
  specialize (H eq_refl). discriminate.
Qed.
Print Assumptions contradictory_array_addresses.
End model.
