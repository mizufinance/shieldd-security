From New.golang Require Import defn.
Require Import GoFieldSyntax GoFieldHeap GoFieldEval.

Inductive executes : @expr field_syntax -> field_heap -> @val field_syntax -> field_heap -> Prop :=
| ExecVal v h : executes (Val v) h v h
| ExecRec binder body h : executes (Rec BAnon binder body) h (RecV BAnon binder body) h
| ExecApp f x h arg h1 binder body h2 result h3 :
    executes x h arg h1 -> executes f h1 (RecV BAnon binder body) h2 ->
    executes (subst' binder arg body) h2 result h3 -> executes (App f x) h result h3
| ExecInstruction f x h arg h1 op h2 result h3 :
    executes x h arg h1 -> executes f h1 (GoInstruction op) h2 ->
    instruction op arg h2 = Some (result, h3) -> executes (App f x) h result h3
| ExecIf cond yes no h b h1 result h2 :
    executes cond h (LitV (LitBool b)) h1 ->
    executes (if b then yes else no) h1 result h2 -> executes (If cond yes no) h result h2
| ExecPair x y h left h1 right h2 :
    executes x h left h1 -> executes y h1 right h2 -> executes (Pair x y) h (PairV left right) h2
| ExecFst e h x y h1 : executes e h (PairV x y) h1 -> executes (Fst e) h x h1
| ExecSnd e h x y h1 : executes e h (PairV x y) h1 -> executes (Snd e) h y h1.

Lemma evaluate_sound fuel : forall e h result h',
  evaluate fuel e h = Some (result, h') -> executes e h result h'.
Proof.
  induction fuel as [|fuel IH]; intros e h result h' H; [discriminate|].
  destruct e; cbn [evaluate] in H; try discriminate.
  - inversion H; subst. constructor.
  - destruct f; [|discriminate]. inversion H; subst. constructor.
  - destruct (evaluate fuel e2 h) as [[arg h1]|] eqn:HX; [|discriminate].
    destruct (evaluate fuel e1 h1) as [[fn h2]|] eqn:HF; [|discriminate].
    destruct fn; try discriminate.
    + destruct f; [|discriminate]. eapply ExecApp; eauto.
    + eapply ExecInstruction; eauto.
  - destruct (evaluate fuel e1 h) as [[cond h1]|] eqn:HC; [|discriminate].
    destruct cond; try discriminate. destruct l; try discriminate.
    eapply ExecIf; eauto.
  - destruct (evaluate fuel e1 h) as [[left h1]|] eqn:HL; [|discriminate].
    destruct (evaluate fuel e2 h1) as [[right h2]|] eqn:HR; [|discriminate].
    inversion H; subst. eapply ExecPair; eauto.
  - destruct (evaluate fuel e h) as [[v h1]|] eqn:HE; [|discriminate].
    destruct v; try discriminate. inversion H; subst. eapply ExecFst; eauto.
  - destruct (evaluate fuel e h) as [[v h1]|] eqn:HE; [|discriminate].
    destruct v; try discriminate. inversion H; subst. eapply ExecSnd; eauto.
Qed.

(* This relation describes the explicit field-slice machine. Native Go/Goose
   adequacy and reached instruction correspondence are separate obligations. *)
