From New.golang Require Import defn.
Require Import GoFieldSyntax GoFieldHeap GoFieldEval.

Lemma evaluate_more fuel : forall e h result,
  evaluate fuel e h = Some result -> evaluate (S fuel) e h = Some result.
Proof.
  induction fuel as [|fuel IH]; intros e h result H; [discriminate|].
  destruct e; cbn [evaluate] in H |- *; try exact H; try discriminate.
  - destruct (evaluate fuel e2 h) as [[arg h1]|] eqn:HX; [|discriminate].
    pose proof (IH _ _ _ HX) as HX'. cbn [evaluate] in HX'. rewrite HX'.
    destruct (evaluate fuel e1 h1) as [[fn h2]|] eqn:HF; [|discriminate].
    pose proof (IH _ _ _ HF) as HF'. cbn [evaluate] in HF'. rewrite HF'.
    destruct fn; try exact H; try discriminate.
    destruct f; [eapply IH; exact H|discriminate].
  - destruct (evaluate fuel e1 h) as [[cond h1]|] eqn:HC; [|discriminate].
    pose proof (IH _ _ _ HC) as HC'. cbn [evaluate] in HC'. rewrite HC'. destruct cond; try discriminate.
    destruct l; try discriminate. destruct b; eapply IH; exact H.
  - destruct (evaluate fuel e1 h) as [[left h1]|] eqn:HL; [|discriminate].
    pose proof (IH _ _ _ HL) as HL'. cbn [evaluate] in HL'. rewrite HL'.
    destruct (evaluate fuel e2 h1) as [[right h2]|] eqn:HR; [|discriminate].
    pose proof (IH _ _ _ HR) as HR'. cbn [evaluate] in HR'. rewrite HR'. exact H.
  - destruct (evaluate fuel e h) as [[v h1]|] eqn:HE; [|discriminate].
    pose proof (IH _ _ _ HE) as HE'. cbn [evaluate] in HE'. rewrite HE'. destruct v; exact H.
  - destruct (evaluate fuel e h) as [[v h1]|] eqn:HE; [|discriminate].
    pose proof (IH _ _ _ HE) as HE'. cbn [evaluate] in HE'. rewrite HE'. destruct v; exact H.
Qed.

Lemma evaluate_monotone fuel extra e h result :
  evaluate fuel e h = Some result -> evaluate (extra + fuel)%nat e h = Some result.
Proof.
  intros H. induction extra; [exact H|cbn; apply evaluate_more; exact IHextra].
Qed.
