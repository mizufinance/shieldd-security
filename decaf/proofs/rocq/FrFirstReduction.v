From Stdlib Require Import ZArith Lia List.
From Core Require Import Core Carry RustMultiply RustFiatPrimitives RustFieldAdd RustMultiplyWords RustMultiplyRow.
From Slice Require Import Decaf_proof_slice_Fiat.
From FrSlice Require Import Decaf_fr_slice_Fiat.
Require Import FrPrefix FrHelpers.
Import ListNotations.
Open Scope Z_scope.
Definition fr_modulus : Z := 2111115437357092606062206234695386632838870926408408195193685246394721360383.
Theorem fr_first_redc_correct row :
  length row = 9%nat -> Forall U32.canonical row ->
  4294967296 * limbs_value (fr_redc_words row) =
    limbs_value row + fr_modulus * ((U32.raw (nth 0 row (0 : t_u32)) * 1893980673) mod 4294967296).
Proof.
  intros Hlen Hcan.
  do 9 (let w := fresh "word" in destruct row as [|w row]; [cbn in Hlen; discriminate|]).
  destruct row; [|cbn in Hlen; discriminate].
  repeat match goal with H : Forall _ (_::_) |- _ => inversion H; subst; clear H end.
  unfold fr_redc_words, fr_native_redc_state. cbn [nth].
  rewrite !fr_multiply_same, !fr_carry_same.
  do 9 row_product.
  change (2^32) with 4294967296 in *.
  change (U32.raw (1893980673 : t_u32)) with 1893980673 in *.
  change (U32.raw (3275741695 : t_u32)) with 3275741695 in *.
  change (U32.raw (3109744282 : t_u32)) with 3109744282 in *.
  change (U32.raw (3292302078 : t_u32)) with 3292302078 in *.
  change (U32.raw (1385407407 : t_u32)) with 1385407407 in *.
  change (U32.raw (2534272000 : t_u32)) with 2534272000 in *.
  change (U32.raw (2553090887 : t_u32)) with 2553090887 in *.
  change (U32.raw (2794137941 : t_u32)) with 2794137941 in *.
  change (U32.raw (78305623 : t_u32)) with 78305623 in *.
  match goal with H : U32.raw ?lo + 4294967296 * U32.raw ?hi = U32.raw ?x * 1893980673 |- _ =>
    assert (Hm : U32.raw lo = (U32.raw x * 1893980673) mod 4294967296) by
      (rewrite <- H; replace (4294967296 * U32.raw hi) with (U32.raw hi * 4294967296) by ring;
       rewrite Z.mod_add by lia; symmetry; apply Z.mod_small; assumption);
    rewrite <- Hm
  end.
  do 7 row_carry.
  match goal with |- context[f_add (cast ?c) ?hi] =>
    remember (f_add (cast c : t_u32) hi) as top eqn:Etop;
    assert (Htop : U32.canonical top) by (subst top; apply add_word_canonical);
    assert (Hadd : U32.raw top = U8.raw c + U32.raw hi) by
      (subst top;
       change ((U8.raw c mod 4294967296 + U32.raw hi) mod 4294967296 = U8.raw c + U32.raw hi);
       rewrite (Z.mod_small (U8.raw c) 4294967296) by lia;
       apply Z.mod_small; lia)
  end.
  match goal with |- context[fq_addcarryx_u32 ?o1 ?o2 ?c ?x ?y] =>
    pose proof (addcarry_reconstruction o1 o2 c x y ltac:(row_word_bound)
      ltac:(row_word_bound) ltac:(row_word_bound)) as Hdiscard;
    destruct (fq_addcarryx_u32 o1 o2 c x y) as [discard carry];
    cbn [fst snd] in Hdiscard; destruct Hdiscard as [Hd [Hc He]];
    change (U8.raw (0 : t_u8)) with 0 in *;
    assert (Hz : U32.raw discard = 0) by
      (unfold U32.canonical, F32.width in *;
       match goal with
       | Hmprod : U32.raw ?m + 4294967296 * U32.raw ?hm = U32.raw ?x * 1893980673,
         Hqprod : U32.raw ?p + 4294967296 * U32.raw ?hp = U32.raw ?m * 3275741695 |- _ =>
         assert (Hmultiple : U32.raw discard = (1444525891*U32.raw x-U32.raw hp-3275741695*U32.raw hm-U8.raw carry)*4294967296) by nia;
         pose proof (f_equal (fun z => z mod 4294967296) Hmultiple) as Hmod;
         cbn beta in Hmod; rewrite Z.mod_mul in Hmod by lia;
         rewrite Z.mod_small in Hmod by assumption; exact Hmod
       end);
    cbn beta iota zeta
  end.
  lazymatch goal with
  | |- context[fq_addcarryx_u32 ?next_o1 ?next_o2 ?next_carry ?next_x ?next_y] =>
    tryif constr_eq next_carry carry then idtac
    else fail "Fr discarded carry is not propagated"
  end.
  do 8 row_carry.
  cbn [fst snd app limbs_value].
  rewrite cast_carry_value by assumption.
  unfold fr_modulus.
  change (2^32) with 4294967296 in *.
  change (U8.raw (0 : t_u8)) with 0 in *.
  clear Etop Hlen Hm.
  repeat match goal with H : _ |- _ => progress (ring_simplify in H) end.
  ring_simplify.
  lia.
Qed.
Print Assumptions fr_first_redc_correct.
