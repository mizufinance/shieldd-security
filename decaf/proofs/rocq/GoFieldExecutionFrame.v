From New.golang Require Import defn.
From Stdlib Require Import List ZArith Lia.
Require Import GoFieldEncoding GoFieldInteger GoFieldSyntax GoFieldTypes GoFieldScalar GoFieldPure GoFieldReference GoFieldHeap GoFieldEval GoFieldBigStep GoFieldClosure GoLiteralDispatch GoFieldHeapFrame GoFieldInstructionFrame GoFieldHelperExecution.
Import ListNotations.

Definition fragment_expr := @field_expr field_syntax (fun _ => true).
Definition fragment_value := @field_value field_syntax (fun _ => true).

Lemma executable_simple e : fragment_expr e = true -> simple_expr e = true.
Proof.
  induction e; cbn [fragment_expr field_expr simple_expr]; try discriminate; try reflexivity.
  - destruct f; [apply IHe|discriminate].
  - intros H. apply andb_true_iff in H as [H1 H2]. rewrite (IHe1 H1) (IHe2 H2). reflexivity.
  - intros H. apply andb_true_iff in H as [H12 H3]. apply andb_true_iff in H12 as [H1 H2].
    rewrite (IHe1 H1) (IHe2 H2) (IHe3 H3). reflexivity.
  - intros H. apply andb_true_iff in H as [H1 H2]. rewrite (IHe1 H1) (IHe2 H2). reflexivity.
  - apply IHe.
  - apply IHe.
Qed.

Lemma executable_substitution x v e : fragment_value v = true -> fragment_expr e = true ->
  fragment_expr (subst x v e) = true.
Proof.
  intros HV. induction e; cbn [fragment_expr field_expr subst]; try discriminate; try tauto.
  - destruct (decide (x = x0)); cbn; auto.
  - destruct f; [|discriminate]. cbn. destruct (decide (BNamed x ≠ BAnon /\ BNamed x ≠ x0)); cbn; auto.
  - intros H. apply andb_true_iff in H as [H1 H2]. rewrite (IHe1 H1) (IHe2 H2). reflexivity.
  - intros H. apply andb_true_iff in H as [H12 H3]. apply andb_true_iff in H12 as [H1 H2].
    rewrite (IHe1 H1) (IHe2 H2) (IHe3 H3). reflexivity.
  - intros H. apply andb_true_iff in H as [H1 H2]. rewrite (IHe1 H1) (IHe2 H2). reflexivity.
Qed.

Lemma executable_substitution_binder binder v e : fragment_value v = true -> fragment_expr e = true ->
  fragment_expr (subst' binder v e) = true.
Proof. destruct binder; [tauto|apply executable_substitution]. Qed.

Lemma scalar_executable kind v : scalar_matches kind v = true -> fragment_value v = true.
Proof.
  destruct kind; cbn [scalar_matches];
    repeat match goal with
    | |- context [decode ?r ?v] => destruct (decode r v) eqn:H
    | |- context [integer_decode ?v] => destruct (integer_decode v) eqn:H
    end; try discriminate; intros _;
    try (apply decode_sound in H as [<- _]; reflexivity);
    apply integer_sound in H; subst; reflexivity.
Qed.

Lemma function_body_executable id : fragment_value (function_body id) = true.
Proof. destruct id; reflexivity. Qed.

Lemma pure_result_executable op arg result :
  pure_instruction op arg = Some result -> fragment_value result = true.
Proof.
  destruct op; cbn [pure_instruction]; try discriminate.
  - unfold typed_conversion. destruct (scalar_type from) as [s|]; [|discriminate].
    destruct (scalar_type to) as [t|]; [|destruct s; discriminate].
    destruct s, t; try (intros H; eapply scalar_executable; eapply conversion_preserves_type; exact H).
    destruct (decide (from = to)); [|discriminate].
    intros H; eapply scalar_executable; eapply conversion_preserves_type; exact H.
  - destruct (scalar_type t) as [kind|]; [|discriminate].
    destruct arg; [destruct kind; discriminate| | | | | | | | | | |];
      try (destruct kind; discriminate).
    destruct kind; unfold decoded_binary, byte_binary, equality_values;
      repeat match goal with
      | |- context [decode ?r ?v] => destruct (decode r v)
      | |- context [word_binary ?s ?op ?x ?y] => destruct (word_binary s op x y) as [[w|b]|]
      end; try discriminate; try (destruct o; try discriminate);
      intros H; inversion H; subst; reflexivity.
  - destruct (scalar_type t) as [kind|]; [|discriminate].
    intros H; eapply scalar_executable; eapply unary_preserves_type; exact H.
  - destruct (scalar_type t) as [kind|], (decode Unit arg); try discriminate.
    intros H; inversion H; subst. apply scalar_executable with kind. apply zero_typed.
Qed.

Lemma instruction_result_executable op arg h result h' :
  instruction op arg h = Some (result, h') -> fragment_value result = true.
Proof.
  destruct op; cbn [instruction];
    try (destruct (pure_instruction _ arg) eqn:HP; [|discriminate];
      intros H; inversion H; subst; eapply pure_result_executable; exact HP).
  - destruct (scalar_type t) as [kind|], (decode Pointer arg) as [pointer|]; try discriminate.
    destruct (read_address h pointer) as [value|]; [|discriminate].
    destruct (scalar_matches kind value) eqn:HV; [|discriminate].
    intros H; inversion H; subst. eapply scalar_executable; exact HV.
  - destruct (scalar_type t) as [kind|]; [|discriminate].
    destruct arg; try discriminate.
    destruct (decode Pointer arg1); [|discriminate].
    destruct (scalar_matches kind arg2); [|discriminate].
    destruct (read_address h c); [|discriminate].
    destruct (scalar_matches kind v); [|discriminate].
    destruct (write_address h c arg2); [|discriminate].
    intros H; inversion H; subst; reflexivity.
  - destruct (scalar_type t) as [kind|]; [|discriminate].
    destruct (scalar_matches kind arg); [|discriminate].
    destruct (allocate_cell h arg). intros H; inversion H; subst; reflexivity.
  - destruct type_args; [|discriminate]. unfold dispatch.
    destruct (resolve f); [|discriminate]. intros H; inversion H; subst.
    apply function_body_executable.
  - destruct t; try discriminate.
    destruct (decide (t = go.uint64 \/ t = go.uint8)); [|discriminate].
    destruct (decode_reference z arg) as [[pointer| | ]|]; try discriminate.
    intros H; inversion H; subst; reflexivity.
Qed.

Lemma executes_result_executable e h result h' : executes e h result h' ->
  fragment_expr e = true -> fragment_value result = true.
Proof.
  intros H. induction H; intros HE; cbn [fragment_expr field_expr] in HE.
  - exact HE.
  - exact HE.
  - apply andb_true_iff in HE as [HF HX].
    apply IHexecutes3. apply executable_substitution_binder; [apply IHexecutes1; exact HX|].
    exact (IHexecutes2 HF).
  - eapply instruction_result_executable; eassumption.
  - apply andb_true_iff in HE as [HCY HN]. apply andb_true_iff in HCY as [HC HY].
    apply IHexecutes2. destruct b; assumption.
  - apply andb_true_iff in HE as [HX HY].
    change (fragment_value left && fragment_value right = true).
    rewrite (IHexecutes1 HX) (IHexecutes2 HY). reflexivity.
  - specialize (IHexecutes HE). apply andb_true_iff in IHexecutes as [HX HY]. exact HX.
  - specialize (IHexecutes HE). apply andb_true_iff in IHexecutes as [HX HY]. exact HY.
Qed.

Lemma executes_framed e h result h' : executes e h result h' ->
  fragment_expr e = true -> forall prefix,
  executes (relocate_expr (length prefix) e) (frame_heap prefix h)
    (relocate_value (length prefix) result) (frame_heap prefix h').
Proof.
  intros H. induction H; intros HE prefix; cbn [fragment_expr field_expr] in HE;
    cbn [relocate_expr relocate_value].
  - constructor.
  - constructor.
  - apply andb_true_iff in HE as [HF HX].
    pose proof (executes_result_executable _ _ _ _ H HX) as HA.
    pose proof (executes_result_executable _ _ _ _ H0 HF) as HB.
    eapply ExecApp.
    + exact (IHexecutes1 HX prefix).
    + exact (IHexecutes2 HF prefix).
    + rewrite <- relocate_substitution_binder; [|apply executable_simple; exact HB].
      apply IHexecutes3. apply executable_substitution_binder; assumption.
  - apply andb_true_iff in HE as [HF HX].
    eapply ExecInstruction.
    + exact (IHexecutes1 HX prefix).
    + exact (IHexecutes2 HF prefix).
    + rewrite instruction_relocated. rewrite H1. reflexivity.
  - apply andb_true_iff in HE as [HCY HN]. apply andb_true_iff in HCY as [HC HY].
    eapply ExecIf.
    + exact (IHexecutes1 HC prefix).
    + destruct b; apply IHexecutes2; assumption.
  - apply andb_true_iff in HE as [HX HY].
    eapply ExecPair; [exact (IHexecutes1 HX prefix)|exact (IHexecutes2 HY prefix)].
  - eapply ExecFst. exact (IHexecutes HE prefix).
  - eapply ExecSnd. exact (IHexecutes HE prefix).
Qed.

Lemma evaluate_framed fuel : forall e h prefix, fragment_expr e = true ->
  evaluate fuel (relocate_expr (length prefix) e) (frame_heap prefix h) =
  option_map (frame_result prefix) (evaluate fuel e h).
Proof.
  induction fuel as [|fuel IH]; intros e h prefix HE; [reflexivity|].
  destruct e; cbn [fragment_expr field_expr] in HE; try discriminate;
    cbn [relocate_expr evaluate].
  - reflexivity.
  - reflexivity.
  - destruct f; [reflexivity|discriminate].
  - apply andb_true_iff in HE as [HF HX].
    rewrite (IH _ _ _ HX).
    destruct (evaluate fuel e2 h) as [[arg h1]|] eqn:HA; [|reflexivity]. cbn [option_map frame_result].
    rewrite (IH _ _ _ HF).
    destruct (evaluate fuel e1 h1) as [[fn h2]|] eqn:HB; [|reflexivity]. cbn [option_map frame_result].
    pose proof (executes_result_executable _ _ _ _ (evaluate_sound _ _ _ _ _ HA) HX) as HArg.
    pose proof (executes_result_executable _ _ _ _ (evaluate_sound _ _ _ _ _ HB) HF) as HFn.
    destruct fn; cbn [relocate_value]; try reflexivity; try (destruct l; reflexivity).
    + destruct f; [|discriminate].
      rewrite <- relocate_substitution_binder; [|apply executable_simple; exact HFn].
      apply IH. apply executable_substitution_binder; assumption.
    + apply instruction_relocated.
  - apply andb_true_iff in HE as [HCY HN]. apply andb_true_iff in HCY as [HC HY].
    rewrite (IH _ _ _ HC).
    destruct (evaluate fuel e1 h) as [[cond h1]|]; [|reflexivity]. cbn [option_map frame_result].
    destruct cond; cbn [relocate_value]; try reflexivity.
    destruct l; try reflexivity. destruct b; apply IH; assumption.
  - apply andb_true_iff in HE as [HX HY].
    rewrite (IH _ _ _ HX).
    destruct (evaluate fuel e1 h) as [[left h1]|]; [|reflexivity]. cbn [option_map frame_result].
    rewrite (IH _ _ _ HY).
    destruct (evaluate fuel e2 h1) as [[right h2]|]; reflexivity.
  - rewrite (IH _ _ _ HE).
    destruct (evaluate fuel e h) as [[v h1]|]; [|reflexivity]. cbn [option_map frame_result].
    destruct v; cbn [relocate_value]; try reflexivity. destruct l; reflexivity.
  - rewrite (IH _ _ _ HE).
    destruct (evaluate fuel e h) as [[v h1]|]; [|reflexivity]. cbn [option_map frame_result].
    destruct v; cbn [relocate_value]; try reflexivity. destruct l; reflexivity.
Qed.

Lemma pointer_free_call_frame fuel e result :
  fragment_expr e = true ->
  (forall k, relocate_expr k e = e) ->
  (forall k, relocate_value k result = result) ->
  option_map fst (evaluate fuel e []) = Some result ->
  forall prefix, exists locals, evaluate fuel e prefix = Some (result, prefix ++ locals).
Proof.
  intros HE HF HR HX prefix.
  destruct (evaluate fuel e []) as [[value heap]|] eqn:EV; [|discriminate].
  inversion HX; subst value.
  exists (relocate_heap (length prefix) heap).
  pose proof (evaluate_framed fuel e [] prefix HE) as H.
  rewrite HF EV in H. cbn [option_map frame_result] in H. rewrite HR in H.
  replace (frame_heap prefix []) with prefix in H by (unfold frame_heap, relocate_heap; cbn; symmetry; apply app_nil_r).
  exact H.
Qed.

Lemma actual_add_any_heap x y carry h :
  exists locals, evaluate 160 (add_call x y carry) h = Some (add_result x y carry, h ++ locals).
Proof. apply pointer_free_call_frame; [reflexivity|reflexivity|reflexivity|apply actual_add_executes]. Qed.

Lemma actual_sub_any_heap x y borrow h :
  exists locals, evaluate 160 (sub_call x y borrow) h = Some (sub_result x y borrow, h ++ locals).
Proof. apply pointer_free_call_frame; [reflexivity|reflexivity|reflexivity|apply actual_sub_executes]. Qed.

Lemma actual_mul_any_heap x y h :
  exists locals, evaluate 240 (mul_call x y) h = Some (mul_result x y, h ++ locals).
Proof. apply pointer_free_call_frame; [reflexivity|reflexivity|reflexivity|apply actual_mul_executes]. Qed.

(* Conditional framing of the explicit field evaluator only. The fragment
   predicate admits resolver names that may fail to resolve. These proofs
   do not assert progress, native adequacy, or allocation/resource bounds.
   Arrays and sum payloads are not recursively relocated. *)
