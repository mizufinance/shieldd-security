From Stdlib Require Import ZArith Lia List.
From Core Require Import Core.
Import ListNotations.
Open Scope Z_scope.

Lemma update_length {A} (a : list A) i v :
  index_defined a i -> length (update_at_usize a i v) = length a.
Proof.
  intros [_ Hi]. unfold update_at_usize.
  rewrite length_app, length_firstn. cbn [length]. rewrite length_skipn.
  assert (Hn : (Z.to_nat (U64.value i) < length a)%nat).
  { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
  rewrite Nat.min_l by lia. lia.
Qed.

Definition indices8 : list t_usize :=
  map U64.of_Z [0;1;2;3;4;5;6;7].

Lemma indices8_safe {A} (a : list A) :
  length a = 8%nat -> Forall (index_defined a) indices8.
Proof.
  intros Hlen. unfold indices8. cbn [map].
  repeat (apply Forall_cons;
    [unfold index_defined, U64.canonical, U64.value, U64.raw, U64.of_Z,
      F64.width, F64.signed; rewrite Hlen; vm_compute; intuition discriminate|]).
  apply Forall_nil.
Qed.

Fixpoint writes_safe {A} (a : list A) (writes : list (t_usize * A)) : Prop :=
  match writes with
  | [] => True
  | (i,v)::rest => index_defined a i /\ writes_safe (update_at_usize a i v) rest
  end.

Lemma writes_preserve_bounds {A} (a : list A) writes :
  Forall (fun p => index_defined a (fst p)) writes -> writes_safe a writes.
Proof.
  revert a. induction writes as [|[i v] rest IH]; intros a H; [exact I|].
  inversion H as [|? ? Hi Hr]; subst. cbn [fst] in Hi.
  split; [exact Hi|]. apply IH.
  apply Forall_forall. intros [j w] Hin. cbn [fst].
  rewrite Forall_forall in Hr. specialize (Hr (j,w) Hin). cbn [fst] in Hr.
  unfold index_defined in *. rewrite update_length by exact Hi. exact Hr.
Qed.

Lemma writes8_safe {A} (a : list A) (values : list A) :
  length a = 8%nat -> writes_safe a (combine indices8 values).
Proof.
  intros Hlen. apply writes_preserve_bounds.
  pose proof (indices8_safe a Hlen) as H.
  apply Forall_forall. intros [i v] Hin. cbn [fst].
  rewrite Forall_forall in H. apply H.
  eapply in_combine_l. exact Hin.
Qed.
