From Stdlib Require Import ZArith Lia List.
From Core Require Import Core Carry RustMultiply RustFiatPrimitives RustFieldAdd RustMultiplyWords RustMultiplyRow RustMultiplyRound.
From Slice Require Import Decaf_proof_slice_Fiat NativeMultiplyPrefix.
Require Import FrPrefix FrFirstReduction FrReductionBounds FrRoundDefinition FrRound.
Import ListNotations.
Open Scope Z_scope.
Fixpoint fr_native_rounds (digits b acc : list t_u32) : list t_u32 :=
  match digits with [] => acc | digit::rest => fr_native_rounds rest b (fr_native_round digit b acc) end.

Theorem fr_rounds_correct digits b :
  Forall U32.canonical digits -> length b = 8%nat -> Forall U32.canonical b ->
  0 <= limbs_value b < fr_modulus ->
  forall acc, length acc = 9%nat -> Forall U32.canonical acc ->
  0 <= limbs_value acc < 2 * fr_modulus ->
  let result := fr_native_rounds digits b acc in
  length result = 9%nat /\ Forall U32.canonical result /\
  0 <= limbs_value result < 2 * fr_modulus /\
  exists k, 4294967296 ^ (Z.of_nat (length digits)) * limbs_value result =
    limbs_value acc + limbs_value digits * limbs_value b + fr_modulus * k.
Proof.
  intros Hdigits Hb Hcb Hbv.
  induction Hdigits as [|digit rest Hd Hrest IH]; intros acc Ha Hca Hav.
  - cbn [fr_native_rounds]. split; [assumption|]. split; [assumption|].
    split; [assumption|]. exists 0.
    change (1 * limbs_value acc = limbs_value acc + 0 * limbs_value b + fr_modulus * 0).
    ring.
  - destruct (fr_round_shape digit b acc Hd Hb Ha Hcb Hca) as [Htlen Htcan].
    pose proof (fr_round_bound digit b acc Hd Hb Ha Hcb Hca Hbv Hav) as Htbound.
    destruct (fr_round_correct digit b acc Hd Hb Ha Hcb Hca) as [m [Hm Hstep]].
    destruct (IH (fr_native_round digit b acc) Htlen Htcan Htbound)
      as [Hrlen [Hrcan [Hrbound [k Hchain]]]].
    cbn [fr_native_rounds]. split; [exact Hrlen|]. split; [exact Hrcan|].
    split; [exact Hrbound|]. exists (m + 4294967296*k).
    cbn [length limbs_value].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    rewrite <- Z.mul_assoc, Hchain.
    rewrite Z.mul_add_distr_l, Z.mul_add_distr_l, Hstep.
    ring.
Qed.
Print Assumptions fr_rounds_correct.

Definition fr_native_accumulate (a b : list t_u32) :=
  fr_native_rounds (tl a) b (fr_redc_words (native_first_row a b)).

Theorem fr_accumulator_correct a b :
  length a = 8%nat -> length b = 8%nat ->
  Forall U32.canonical a -> Forall U32.canonical b ->
  0 <= limbs_value b < fr_modulus ->
  let result := fr_native_accumulate a b in
  length result = 9%nat /\ Forall U32.canonical result /\
  0 <= limbs_value result < 2 * fr_modulus /\
  exists k, 4294967296 ^ 8 * limbs_value result =
    limbs_value a * limbs_value b + fr_modulus * k.
Proof.
  intros Ha Hb Hca Hcb Hbv.
  destruct a as [|digit rest]; [discriminate|].
  assert (Hrlen : length rest = 7%nat) by (cbn in Ha; lia).
  inversion Hca as [|? ? Hd Hrest]; subst.
  set (product := native_first_row (digit::rest) b).
  pose proof (first_row_length (digit::rest) b) as Hplen. fold product in Hplen.
  pose proof (first_row_words (digit::rest) b Ha Hb Hca Hcb) as Hpcan. fold product in Hpcan.
  pose proof (first_row_correct (digit::rest) b Ha Hb Hca Hcb) as Hpvalue.
  change (limbs_value product = U32.raw digit * limbs_value b) in Hpvalue.
  assert (Hpbound : 0 <= limbs_value product < (4294967296+1)*fr_modulus).
  { rewrite Hpvalue. unfold U32.canonical, F32.width, fr_modulus in *. nia. }
  set (s0 := fr_redc_words product).
  pose proof (fr_first_redc_length product Hplen) as Hl0. fold s0 in Hl0.
  pose proof (fr_first_redc_words product Hplen Hpcan) as Hc0. fold s0 in Hc0.
  pose proof (fr_first_redc_bound product Hplen Hpcan Hpbound) as Hv0. fold s0 in Hv0.
  pose proof (fr_first_redc_correct product Hplen Hpcan) as He0.
  set (m0 := (U32.raw (nth 0 product (0:t_u32)) * 1893980673) mod 4294967296).
  change (4294967296 * limbs_value s0 = limbs_value product + fr_modulus*m0) in He0.
  rewrite Hpvalue in He0.
  destruct (fr_rounds_correct rest b Hrest Hb Hcb Hbv s0 Hl0 Hc0 Hv0)
    as [Hlen [Hcan [Hbound [k Hchain]]]].
  rewrite Hrlen in Hchain.
  change (4294967296^7 * limbs_value (fr_native_rounds rest b s0) =
    limbs_value s0 + limbs_value rest * limbs_value b + fr_modulus*k) in Hchain.
  unfold fr_native_accumulate. cbn [tl]. fold product. fold s0.
  split; [exact Hlen|]. split; [exact Hcan|]. split; [exact Hbound|].
  exists (m0 + 4294967296*k).
  change ((4294967296 * 4294967296^7) * limbs_value (fr_native_rounds rest b s0) =
    (U32.raw digit + 4294967296*limbs_value rest)*limbs_value b + fr_modulus*(m0+4294967296*k)).
  rewrite <- Z.mul_assoc, Hchain.
  rewrite Z.mul_add_distr_l, Z.mul_add_distr_l, He0.
  ring.
Qed.
Print Assumptions fr_accumulator_correct.
