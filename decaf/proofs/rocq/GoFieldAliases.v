From New.code.mizufinance_local.decaf Require Import fiat.
From New.golang.theory Require Import auto array.
From Stdlib Require Import ZArith Lia List.
Require Import GoFieldAdd.
Open Scope Z_scope.

Definition sum_spec (result : array.t w64 4) (xs ys : list w64) : Prop :=
  0 <= limbs_value (array.arr result) < fq_modulus /\
  limbs_value (array.arr result) = (limbs_value xs + limbs_value ys) mod fq_modulus.

Section aliases.
Context `{ffi_sem : ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}
  `{!fiat.FqUint1_Assumptions}
  `{!FuncUnfold bits.Add64 [] bits.Add64ⁱᵐᵖˡ}
  `{!FuncUnfold bits.Sub64 [] bits.Sub64ⁱᵐᵖˡ}
  `{!FuncUnfold fiat.FqCmovznzU64 [] fiat.FqCmovznzU64ⁱᵐᵖˡ}.

Lemma add_disjoint out p q (a b c d e f g h o0 o1 o2 o3 : w64) :
  0 <= limbs_value [a;b;c;d] < fq_modulus ->
  0 <= limbs_value [e;f;g;h] < fq_modulus ->
  {{{ out ↦ array.mk 4 [o0;o1;o2;o3] ∗ p ↦ array.mk 4 [a;b;c;d] ∗
      q ↦ array.mk 4 [e;f;g;h] }}}
    fiat.FqAddⁱᵐᵖˡ #out #p #q
  {{{ (result : array.t w64 4), RET #(); out ↦ result ∗
      (p ↦ array.mk 4 [a;b;c;d] ∗ q ↦ array.mk 4 [e;f;g;h]) ∗
      ⌜sum_spec result [a;b;c;d] [e;f;g;h]⌝ }}}.
Proof.
  intros Ha Hb. iIntros (Φ) "(Hout & Hp & Hq) HΦ".
  wp_apply (add_correct out p q (DfracOwn 1) (DfracOwn 1)
    a b c d e f g h o0 o1 o2 o3
    (p ↦ array.mk 4 [a;b;c;d] ∗ q ↦ array.mk 4 [e;f;g;h]) Ha Hb
    with "[Hout Hp Hq]").
  { iFrame "Hp Hq". iIntros "[Hp Hq]". iFrame. }
  iIntros (result) "Hresult". iApply "HΦ". iExact "Hresult".
Qed.

Lemma add_left p q dq (a b c d e f g h : w64) :
  0 <= limbs_value [a;b;c;d] < fq_modulus ->
  0 <= limbs_value [e;f;g;h] < fq_modulus ->
  {{{ p ↦ array.mk 4 [a;b;c;d] ∗ q ↦{dq} array.mk 4 [e;f;g;h] }}}
    fiat.FqAddⁱᵐᵖˡ #p #p #q
  {{{ (result : array.t w64 4), RET #(); p ↦ result ∗
      q ↦{dq} array.mk 4 [e;f;g;h] ∗ ⌜sum_spec result [a;b;c;d] [e;f;g;h]⌝ }}}.
Proof.
  intros Ha Hb. iIntros (Φ) "[Hp Hq] HΦ".
  wp_apply (add_correct p p q (DfracOwn 1) dq a b c d e f g h a b c d
    (q ↦{dq} array.mk 4 [e;f;g;h]) Ha Hb with "[Hp Hq]").
  { iFrame. iIntros "[Hp Hq]". iFrame. }
  iIntros (result) "Hresult". iApply "HΦ". iExact "Hresult".
Qed.

Lemma add_right p q dq (a b c d e f g h : w64) :
  0 <= limbs_value [a;b;c;d] < fq_modulus ->
  0 <= limbs_value [e;f;g;h] < fq_modulus ->
  {{{ p ↦{dq} array.mk 4 [a;b;c;d] ∗ q ↦ array.mk 4 [e;f;g;h] }}}
    fiat.FqAddⁱᵐᵖˡ #q #p #q
  {{{ (result : array.t w64 4), RET #(); q ↦ result ∗
      p ↦{dq} array.mk 4 [a;b;c;d] ∗ ⌜sum_spec result [a;b;c;d] [e;f;g;h]⌝ }}}.
Proof.
  intros Ha Hb. iIntros (Φ) "[Hp Hq] HΦ".
  wp_apply (add_correct q p q dq (DfracOwn 1) a b c d e f g h e f g h
    (p ↦{dq} array.mk 4 [a;b;c;d]) Ha Hb with "[Hp Hq]").
  { iFrame. iIntros "[Hp Hq]". iFrame. }
  iIntros (result) "Hresult". iApply "HΦ". iExact "Hresult".
Qed.

Lemma add_all_equal p (a b c d : w64) :
  0 <= limbs_value [a;b;c;d] < fq_modulus ->
  {{{ p ↦ array.mk 4 [a;b;c;d] }}}
    fiat.FqAddⁱᵐᵖˡ #p #p #p
  {{{ (result : array.t w64 4), RET #(); p ↦ result ∗
      ⌜sum_spec result [a;b;c;d] [a;b;c;d]⌝ }}}.
Proof.
  intros Ha. iIntros (Φ) "Hp HΦ".
  iDestruct "Hp" as "[Hp Hq]".
  wp_apply (add_correct p p p (DfracOwn (1/2)%Qp) (DfracOwn (1/2)%Qp)
    a b c d a b c d a b c d emp Ha Ha with "[Hp Hq]").
  { iFrame. iIntros "[Hp Hq]". iCombine "Hp Hq" as "Hp". iFrame. }
  iIntros (result) "(Hp & _ & %Hresult)". iApply "HΦ". iFrame. done.
Qed.

Lemma add_equal_inputs out p (a b c d o0 o1 o2 o3 : w64) :
  0 <= limbs_value [a;b;c;d] < fq_modulus ->
  {{{ out ↦ array.mk 4 [o0;o1;o2;o3] ∗ p ↦ array.mk 4 [a;b;c;d] }}}
    fiat.FqAddⁱᵐᵖˡ #out #p #p
  {{{ (result : array.t w64 4), RET #(); out ↦ result ∗ p ↦ array.mk 4 [a;b;c;d] ∗
      ⌜sum_spec result [a;b;c;d] [a;b;c;d]⌝ }}}.
Proof.
  intros Ha. iIntros (Φ) "[Hout Hp] HΦ".
  iDestruct "Hp" as "[Hp Hq]".
  wp_apply (add_correct out p p (DfracOwn (1/2)%Qp) (DfracOwn (1/2)%Qp)
    a b c d a b c d o0 o1 o2 o3 (p ↦ array.mk 4 [a;b;c;d]) Ha Ha
    with "[Hout Hp Hq]").
  { iFrame "Hp Hq". iIntros "[Hp Hq]". iCombine "Hp Hq" as "Hp". iFrame. }
  iIntros (result) "Hresult". iApply "HΦ". iExact "Hresult".
Qed.
End aliases.
