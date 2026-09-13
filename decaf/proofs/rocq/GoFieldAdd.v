From New.code.mizufinance_local.decaf Require Import fiat.
From New.golang.theory Require Import auto array.
From Stdlib Require Import ZArith Lia List.
Require Import GoArray GoCarry GoBorrow GoSelect.
Open Scope Z_scope.
Definition fq_modulus : Z :=
  8444461749428370424248824938781546531375899335154063827935233455917409239041.
Fixpoint limbs_value (xs : list w64) : Z :=
  match xs with [] => 0 | x::xs => word.unsigned x + 2^64 * limbs_value xs end.
Section field.
Context `{ffi_sem : ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}
  `{!fiat.FqUint1_Assumptions}
  `{!FuncUnfold bits.Add64 [] bits.Add64ⁱᵐᵖˡ}
  `{!FuncUnfold bits.Sub64 [] bits.Sub64ⁱᵐᵖˡ}
  `{!FuncUnfold fiat.FqCmovznzU64 [] fiat.FqCmovznzU64ⁱᵐᵖˡ}.
(* Exact resolver equations for the freshly extracted call inventory.
   A concrete interpretation satisfying these equations and the named-type
   contracts is still required; closed global assumptions do not supply it. *)
(* All input reads finish before the first output write. The wand returns
   exclusive output ownership after those reads, allowing the alias corollaries
   to split and recombine read ownership without assuming disjoint inputs. *)
Lemma add_correct out p q dq1 dq2 (a b c d e f g h o0 o1 o2 o3 : w64) (R : iProp Σ) :
  0 <= limbs_value [a;b;c;d] < fq_modulus ->
  0 <= limbs_value [e;f;g;h] < fq_modulus ->
  {{{ p ↦{dq1} array.mk 4 [a;b;c;d] ∗ q ↦{dq2} array.mk 4 [e;f;g;h] ∗
      ((p ↦{dq1} array.mk 4 [a;b;c;d] ∗ q ↦{dq2} array.mk 4 [e;f;g;h]) -∗
        out ↦ array.mk 4 [o0;o1;o2;o3] ∗ R) }}}
    fiat.FqAddⁱᵐᵖˡ #out #p #q
  {{{ (result : array.t w64 4), RET #(); out ↦ result ∗ R ∗
    ⌜0 <= limbs_value (array.arr result) < fq_modulus /\
      limbs_value (array.arr result) =
        (limbs_value [a;b;c;d] + limbs_value [e;f;g;h]) mod fq_modulus⌝ }}}.
Proof.
  intros Hva Hvb. pose proof (go.tagged_steps internal).
  wp_start as "[Harg1 [Harg2 Hout]]".
  iEval (rewrite typed_pointsto_unseal_eq /=) in "Harg1".
  iEval (rewrite typed_pointsto_unseal_eq /=) in "Harg2".
  iDestruct "Harg1" as "[[_ [Ha [Hb [Hc [Hd _]]]]] %Hp]".
  iDestruct "Harg2" as "[[_ [He [Hf [Hg [Hh _]]]]] %Hq]".
  array_steps. wp_func_call.
  wp_apply (addcarry_correct with "[]"); first word.
  iIntros (x1 x2) "%H1". destruct H1 as [H1 [L1 C1]].
  array_steps. wp_func_call.
  wp_apply (addcarry_correct with "[]"); first lia.
  iIntros (x3 x4) "%H2". destruct H2 as [H2 [L2 C2]].
  array_steps. wp_func_call.
  wp_apply (addcarry_correct with "[]"); first lia.
  iIntros (x5 x6) "%H3". destruct H3 as [H3 [L3 C3]].
  array_steps. wp_func_call.
  wp_apply (addcarry_correct with "[]"); first lia.
  iIntros (x7 x8) "%H4". destruct H4 as [H4 [L4 C4]].
  iSpecialize ("Hout" with "[Ha Hb Hc Hd He Hf Hg Hh]").
  { iSplitL "Ha Hb Hc Hd"; iApply typed_pointsto_combine; try done; simpl; iFrame; done. }
  iDestruct "Hout" as "[Hout HR]".
  iEval (rewrite typed_pointsto_unseal_eq /=) in "Hout".
  iDestruct "Hout" as "[[_ [Ho0 [Ho1 [Ho2 [Ho3 _]]]]] %Hout]".
  array_steps. wp_func_call.
  wp_apply (subborrow_correct with "[]"); first word.
  iIntros (x9 x10) "%H5". destruct H5 as [H5 [L5 C5]].
  array_steps. wp_func_call.
  wp_apply (subborrow_correct with "[]"); first lia.
  iIntros (x11 x12) "%H6". destruct H6 as [H6 [L6 C6]].
  array_steps. wp_func_call.
  wp_apply (subborrow_correct with "[]"); first lia.
  iIntros (x13 x14) "%H7". destruct H7 as [H7 [L7 C7]].
  array_steps. wp_func_call.
  wp_apply (subborrow_correct with "[]"); first lia.
  iIntros (x15 x16) "%H8". destruct H8 as [H8 [L8 C8]].
  array_steps. wp_func_call.
  wp_apply (subborrow_correct with "[]"); first lia.
  iIntros (x17 x18) "%H9". destruct H9 as [H9 [L9 C9]].
  array_steps. wp_func_call.
  wp_apply (select_correct with "[$]"); first lia.
  iIntros "Hx19".
  array_steps. wp_func_call.
  wp_apply (select_correct with "[$]"); first lia.
  iIntros "Hx20".
  array_steps. wp_func_call.
  wp_apply (select_correct with "[$]"); first lia.
  iIntros "Hx21".
  array_steps. wp_func_call.
  wp_apply (select_correct with "[$]"); first lia.
  iIntros "Hx22".
  destruct (decide (word.unsigned x18 = 0)) as [Hchoice|Hchoice].
  all: array_steps.
  - iApply ("HΦ" $! (array.mk 4 [x9;x11;x13;x15])).
    iSplitL "Ho0 Ho1 Ho2 Ho3".
    { iApply typed_pointsto_combine; first done. simpl. iFrame. done. }
    iFrame "HR". iPureIntro.
    unfold fq_modulus in *.
    cbn [limbs_value array.arr] in *.
    change (2^64) with 18446744073709551616 in *.
    change (word.unsigned (W64 0)) with 0 in *.
    change (word.unsigned (W64 725501752471715841)) with 725501752471715841 in *.
    change (word.unsigned (W64 6461107452199829505)) with 6461107452199829505 in *.
    change (word.unsigned (W64 6968279316240510977)) with 6968279316240510977 in *.
    change (word.unsigned (W64 1345280370688173398)) with 1345280370688173398 in *.
    split; [lia|apply Z.mod_unique with (q := 1); lia].
  - iApply ("HΦ" $! (array.mk 4 [x1;x3;x5;x7])).
    iSplitL "Ho0 Ho1 Ho2 Ho3".
    { iApply typed_pointsto_combine; first done. simpl. iFrame. done. }
    iFrame "HR". iPureIntro.
    unfold fq_modulus in *.
    cbn [limbs_value array.arr] in *.
    change (2^64) with 18446744073709551616 in *.
    change (word.unsigned (W64 0)) with 0 in *.
    change (word.unsigned (W64 725501752471715841)) with 725501752471715841 in *.
    change (word.unsigned (W64 6461107452199829505)) with 6461107452199829505 in *.
    change (word.unsigned (W64 6968279316240510977)) with 6968279316240510977 in *.
    change (word.unsigned (W64 1345280370688173398)) with 1345280370688173398 in *.
    split; [lia|apply Z.mod_unique with (q := 0); lia].
Qed.
End field.
