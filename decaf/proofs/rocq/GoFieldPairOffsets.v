From New.code.mizufinance_local.decaf Require Import fiat.
From New.golang.theory Require Import auto array.
From Stdlib Require Import ZArith Lia List.
Require Import GoArrayWindows GoFieldAdd GoFieldAliases.
Open Scope Z_scope.

Section offsets.
Context `{ffi_sem : ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}
  `{!fiat.FqUint1_Assumptions}
  `{!FuncUnfold bits.Add64 [] bits.Add64ⁱᵐᵖˡ}
  `{!FuncUnfold bits.Sub64 [] bits.Sub64ⁱᵐᵖˡ}
  `{!FuncUnfold fiat.FqCmovznzU64 [] fiat.FqCmovznzU64ⁱᵐᵖˡ}.

Lemma add_input_windows base out (xs preP postP preQ postQ : list w64)
    (a b c d e f g h o0 o1 o2 o3 : w64) :
  xs = preP ++ [a;b;c;d] ++ postP ->
  xs = preQ ++ [e;f;g;h] ++ postQ ->
  0 <= limbs_value [a;b;c;d] < fq_modulus ->
  0 <= limbs_value [e;f;g;h] < fq_modulus ->
  {{{ base ↦ array.mk (Z.of_nat (length xs)) xs ∗ out ↦ array.mk 4 [o0;o1;o2;o3] }}}
    fiat.FqAddⁱᵐᵖˡ #out
      #(array_index_ref w64 (Z.of_nat (length preP)) base)
      #(array_index_ref w64 (Z.of_nat (length preQ)) base)
  {{{ (result : array.t w64 4), RET #(); out ↦ result ∗
      base ↦ array.mk (Z.of_nat (length xs)) xs ∗
      ⌜sum_spec result [a;b;c;d] [e;f;g;h]⌝ }}}.
Proof.
  intros Hp Hq Ha Hb. iIntros (Φ) "[H Hout] HΦ".
  iDestruct "H" as "[HP HQ]".
  iEval (rewrite Hp) in "HP". iEval (rewrite Hq) in "HQ".
  iDestruct (array_window4 base (DfracOwn (1/2)%Qp) preP [a;b;c;d] postP eq_refl with "HP") as "[HP RP]".
  iDestruct (array_window4 base (DfracOwn (1/2)%Qp) preQ [e;f;g;h] postQ eq_refl with "HQ") as "[HQ RQ]".
  wp_apply (add_correct out _ _ (DfracOwn (1/2)%Qp) (DfracOwn (1/2)%Qp)
    a b c d e f g h o0 o1 o2 o3 (base ↦ array.mk (Z.of_nat (length xs)) xs) Ha Hb
    with "[HP HQ RP RQ Hout]").
  { iFrame "HP HQ". iIntros "[HP HQ]".
    iSpecialize ("RP" $! (array.mk 4 [a;b;c;d]) with "HP").
    iSpecialize ("RQ" $! (array.mk 4 [e;f;g;h]) with "HQ").
    iEval (rewrite /= -Hp) in "RP". iEval (rewrite /= -Hq) in "RQ".
    iCombine "RP RQ" as "H". iFrame. }
  iIntros (result) "H". iApply "HΦ". iExact "H".
Qed.

Lemma add_left_window base q dq (xs preP postP preO postO : list w64)
    (a b c d e f g h o0 o1 o2 o3 : w64) :
  xs = preP ++ [a;b;c;d] ++ postP ->
  xs = preO ++ [o0;o1;o2;o3] ++ postO ->
  0 <= limbs_value [a;b;c;d] < fq_modulus ->
  0 <= limbs_value [e;f;g;h] < fq_modulus ->
  {{{ base ↦ array.mk (Z.of_nat (length xs)) xs ∗ q ↦{dq} array.mk 4 [e;f;g;h] }}}
    fiat.FqAddⁱᵐᵖˡ #(array_index_ref w64 (Z.of_nat (length preO)) base)
      #(array_index_ref w64 (Z.of_nat (length preP)) base) #q
  {{{ (result : array.t w64 4), RET #();
      base ↦ array.mk (Z.of_nat (length xs)) (preO ++ array.arr result ++ postO) ∗
      q ↦{dq} array.mk 4 [e;f;g;h] ∗ ⌜sum_spec result [a;b;c;d] [e;f;g;h]⌝ }}}.
Proof.
  intros Hp Ho Ha Hb. iIntros (Φ) "[H HQ] HΦ".
  iEval (rewrite Hp) in "H".
  iDestruct (array_window4 base (DfracOwn 1) preP [a;b;c;d] postP eq_refl with "H") as "[HP RP]".
  set (R := (q ↦{dq} array.mk 4 [e;f;g;h] ∗
    (∀ result : array.t w64 4,
      array_index_ref w64 (Z.of_nat (length preO)) base ↦ result -∗
      base ↦ array.mk (Z.of_nat (length xs)) (preO ++ array.arr result ++ postO)))%I).
  wp_apply (add_correct _ _ q (DfracOwn 1) dq
    a b c d e f g h o0 o1 o2 o3 R Ha Hb with "[HP HQ RP]").
  { iFrame "HP HQ". iIntros "[HP HQ]".
    iSpecialize ("RP" $! (array.mk 4 [a;b;c;d]) with "HP").
    iEval (rewrite /= -Hp Ho) in "RP".
    iDestruct (array_window4 base (DfracOwn 1) preO [o0;o1;o2;o3] postO eq_refl with "RP") as "[Hout RO]".
    iFrame "Hout". unfold R. iFrame "HQ".
    iIntros (result) "Hout". iSpecialize ("RO" $! result with "Hout").
    rewrite Ho. iExact "RO". }
  iIntros (result) "(Hout & HR & %Hspec)".
  iEval (unfold R) in "HR". iDestruct "HR" as "[HQ HR]".
  iSpecialize ("HR" $! result with "Hout").
  iApply "HΦ". iFrame. done.
Qed.

Lemma add_right_window base p dq (xs preQ postQ preO postO : list w64)
    (a b c d e f g h o0 o1 o2 o3 : w64) :
  xs = preQ ++ [e;f;g;h] ++ postQ ->
  xs = preO ++ [o0;o1;o2;o3] ++ postO ->
  0 <= limbs_value [a;b;c;d] < fq_modulus ->
  0 <= limbs_value [e;f;g;h] < fq_modulus ->
  {{{ base ↦ array.mk (Z.of_nat (length xs)) xs ∗ p ↦{dq} array.mk 4 [a;b;c;d] }}}
    fiat.FqAddⁱᵐᵖˡ #(array_index_ref w64 (Z.of_nat (length preO)) base)
      #p #(array_index_ref w64 (Z.of_nat (length preQ)) base)
  {{{ (result : array.t w64 4), RET #();
      base ↦ array.mk (Z.of_nat (length xs)) (preO ++ array.arr result ++ postO) ∗
      p ↦{dq} array.mk 4 [a;b;c;d] ∗ ⌜sum_spec result [a;b;c;d] [e;f;g;h]⌝ }}}.
Proof.
  intros Hq Ho Ha Hb. iIntros (Φ) "[H HP] HΦ".
  iEval (rewrite Hq) in "H".
  iDestruct (array_window4 base (DfracOwn 1) preQ [e;f;g;h] postQ eq_refl with "H") as "[HQ RQ]".
  set (R := (p ↦{dq} array.mk 4 [a;b;c;d] ∗
    (∀ result : array.t w64 4,
      array_index_ref w64 (Z.of_nat (length preO)) base ↦ result -∗
      base ↦ array.mk (Z.of_nat (length xs)) (preO ++ array.arr result ++ postO)))%I).
  wp_apply (add_correct _ p _ dq (DfracOwn 1)
    a b c d e f g h o0 o1 o2 o3 R Ha Hb with "[HP HQ RQ]").
  { iFrame "HP HQ". iIntros "[HP HQ]".
    iSpecialize ("RQ" $! (array.mk 4 [e;f;g;h]) with "HQ").
    iEval (rewrite /= -Hq Ho) in "RQ".
    iDestruct (array_window4 base (DfracOwn 1) preO [o0;o1;o2;o3] postO eq_refl with "RQ") as "[Hout RO]".
    iFrame "Hout". unfold R. iFrame "HP".
    iIntros (result) "Hout". iSpecialize ("RO" $! result with "Hout").
    rewrite Ho. iExact "RO". }
  iIntros (result) "(Hout & HR & %Hspec)".
  iEval (unfold R) in "HR". iDestruct "HR" as "[HP HR]".
  iSpecialize ("HR" $! result with "Hout").
  iApply "HΦ". iFrame. done.
Qed.
End offsets.
