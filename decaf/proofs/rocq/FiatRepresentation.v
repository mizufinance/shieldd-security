From Stdlib Require Import ZArith Lia List.
Require Import FiatEndpoint Crypto.Arithmetic.Core Crypto.Arithmetic.UniformWeight Crypto.Arithmetic.Partition.
Import ListNotations.
Open Scope Z_scope.
Fixpoint word_value (xs : list Z) : Z :=
 match xs with [] => 0 | x::rest => x + 4294967296 * word_value rest end.
Lemma positional_value xs : @AM.eval 32 (length xs) xs = word_value xs.
Proof.
 induction xs as [|x xs IH]; [reflexivity|].
 change (Positional.eval (UniformWeight.uweight 32) (S (length xs)) (x::xs) = x+4294967296*word_value xs).
 rewrite Positional.eval_cons by reflexivity.
 rewrite UniformWeight.uweight_eval_shift by lia.
 rewrite UniformWeight.uweight_0, UniformWeight.uweight_1.
 change (1*x+4294967296*(@AM.eval 32 (length xs) xs)=x+4294967296*word_value xs).
 rewrite IH. ring.
Qed.
Lemma canonical_valid xs : length xs = 8%nat ->
 Forall (fun x => 0 <= x < 4294967296) xs ->
 0 <= word_value xs < FiatMultiply.fq -> AM.valid 32 8 FiatMultiply.fq xs.
Proof.
 intros Hl Hc Hv. split.
 - unfold AM.small, AM.eval.
   apply UniformWeight.uweight_partition_unique; [lia|exact Hl|].
   intros x Hin. rewrite Forall_forall in Hc. specialize (Hc x Hin).
   change (0 <= x <= 4294967296-1). lia.
 - rewrite <- Hl. rewrite positional_value. exact Hv.
Qed.
Lemma partition_words x n :
 Forall (fun z => 0 <= z < 4294967296)
 (Partition.Partition.partition (UniformWeight.uweight 32) n x).
Proof.
 unfold Partition.Partition.partition. apply Forall_map.
 apply Forall_forall. intros i Hin.
 assert (Hw : 0 < UniformWeight.uweight 32 i).
 { rewrite UniformWeight.uweight_eq_alt by lia. apply Z.pow_pos_nonneg; lia. }
 pose proof (Z.mod_pos_bound x (UniformWeight.uweight 32 (S i))) as Hmod.
 rewrite UniformWeight.uweight_S in Hmod by lia.
 change (0 < 4294967296*UniformWeight.uweight 32 i ->
  0 <= x mod (4294967296*UniformWeight.uweight 32 i) < 4294967296*UniformWeight.uweight 32 i) in Hmod.
 specialize (Hmod ltac:(nia)).
 rewrite UniformWeight.uweight_S by lia. change (0 <= x mod (4294967296*UniformWeight.uweight 32 i) / UniformWeight.uweight 32 i < 4294967296).
 split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.
Lemma valid_canonical xs : AM.valid 32 8 FiatMultiply.fq xs ->
 length xs = 8%nat /\ Forall (fun x => 0 <= x < 4294967296) xs /\
 0 <= word_value xs < FiatMultiply.fq.
Proof.
 intros [Hs Hb]. assert (Hl : length xs = 8%nat).
 { eapply AM.length_small; exact Hs. }
 split; [exact Hl|]. split.
 - unfold AM.small in Hs. rewrite Hs. apply partition_words.
 - rewrite <- positional_value, Hl. exact Hb.
Qed.

