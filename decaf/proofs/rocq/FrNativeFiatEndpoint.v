From Stdlib Require Import ZArith Lia List.
From Core Require Import Core RustFieldAdd.
Require Import FrFirstReduction FrComplete.
From FrSlice Require Import Decaf_fr_slice_Fiat.
Require Import FiatMultiply FrFiatEndpoint FrFiatRepresentation MontgomeryBridge Crypto.Util.ZUtil.Modulo.PullPush.
Import ListNotations.
Open Scope Z_scope.
Global Opaque RustFr.body RustFr.correct fiat_mul.
Lemma raw_word_value xs : word_value (map U32.raw xs) = limbs_value xs.
Proof. induction xs; cbn [map word_value limbs_value]; [reflexivity|now rewrite IHxs]. Qed.
Lemma raw_canonical xs : Forall U32.canonical xs ->
 Forall (fun z => 0 <= z < 4294967296) (map U32.raw xs).
Proof. intro H. induction H; cbn [map]; constructor; assumption. Qed.
Lemma raw_valid xs : length xs = 8%nat -> Forall U32.canonical xs ->
 0 <= limbs_value xs < fr_modulus -> AM.valid 32 8 fr (map U32.raw xs).
Proof.
 intros Hl Hc Hv. apply canonical_valid.
 - now rewrite map_length.
 - now apply raw_canonical.
 - rewrite raw_word_value. exact Hv.
Qed.
Lemma word_inverse : (4294967296*inv_word) mod fr = 1.
Proof. vm_compute. reflexivity. Qed.
Lemma decoder_unit : exists t, 4294967296^8 * inv_word^8 = 1 + fr*t.
Proof.
 apply congruence_witness; [unfold fr; lia|].
 rewrite <- Z.pow_mul_l.
 rewrite Z.mod_pow_full, word_inverse.
 change (1 mod fr = 1 mod fr). reflexivity.
Qed.
Theorem exact_fiat_multiplication out a b :
 length out = 8%nat -> length a = 8%nat -> length b = 8%nat ->
 Forall U32.canonical a -> Forall U32.canonical b ->
 0 <= limbs_value a < fr_modulus -> 0 <= limbs_value b < fr_modulus ->
 map U32.raw (fr_mul out a b) = fiat_mul (map U32.raw a) (map U32.raw b).
Proof.
 intros Ho Ha Hb Hca Hcb Hva Hvb. destruct decoder_unit as [t Hunit].
 pose proof (raw_valid a Ha Hca Hva) as Hva'.
 pose proof (raw_valid b Hb Hcb Hvb) as Hvb'.
 destruct (fr_multiplication_correct out a b Ho Ha Hb Hca Hcb Hvb)
  as [Hnl [Hnc [Hnb [k Hnative]]]].
 pose proof (raw_valid _ Hnl Hnc Hnb) as Hnv.
 destruct (fiat_decoded_product _ _ Hva' Hvb') as [Hfv Hfiat].
 set (nv := map U32.raw (fr_mul out a b)) in *.
 set (fv := fiat_mul (map U32.raw a) (map U32.raw b)) in *.
 assert (Hnl' : length nv = 8%nat) by (unfold nv; now rewrite map_length).
 pose proof (valid_canonical fv Hfv) as [Hfl [Hfc Hfb]].
 assert (Hne : @AM.eval 32 8 nv = limbs_value (fr_mul out a b)).
 { rewrite <- Hnl', positional_value. unfold nv. apply raw_word_value. }
 assert (Hae : @AM.eval 32 8 (map U32.raw a) = limbs_value a).
 { rewrite <- Ha at 1. rewrite <- (map_length U32.raw a), positional_value. apply raw_word_value. }
 assert (Hbe : @AM.eval 32 8 (map U32.raw b) = limbs_value b).
 { rewrite <- Hb at 1. rewrite <- (map_length U32.raw b), positional_value. apply raw_word_value. }
 rewrite Hae, Hbe in Hfiat.
 pose proof (native_decoded_product fr (4294967296^8) (inv_word^8) _
  (limbs_value (fr_mul out a b)) (limbs_value a) (limbs_value b) k
  ltac:(unfold fr; lia) Hunit Hnative) as Hdecoded.
 assert (Heqmod : (@AM.eval 32 8 nv * inv_word^8) mod fr = (@AM.eval 32 8 fv * inv_word^8) mod fr).
 { rewrite Hne, Hdecoded. symmetry. exact Hfiat. }
 pose proof (cancel_decoding fr (4294967296^8) (inv_word^8) _
  (@AM.eval 32 8 nv) (@AM.eval 32 8 fv) ltac:(unfold fr; lia) Hunit Heqmod) as Heq.
 destruct Hnv as [Hns Hnr]. destruct Hfv as [Hfs Hfr].
 rewrite !Z.mod_small in Heq by assumption.
 unfold AM.small in Hns, Hfs. rewrite Hns, Hfs. now rewrite Heq.
Qed.


