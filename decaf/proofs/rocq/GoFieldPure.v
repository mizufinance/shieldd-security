From New.golang Require Import defn.
Require Import GoFieldEncoding GoFieldInteger GoFieldSyntax GoFieldTypes GoFieldScalar.

Definition scalar_unary k op (v : @val field_syntax) : option val :=
  match k with
  | U64 | I64 =>
    match decode Uint64 v with
    | Some x => match op with
      | GoPos => Some v
      | GoNeg => Some (encode Uint64 (word.opp x))
      | GoComplement => Some (encode Uint64 (word.not x))
      | GoNot => None end
    | None => None end
  | Boolean => match decode Bool v, op with
    | Some b, GoNot => Some (encode Bool (negb b))
    | _, _ => None end
  | Integer => match integer_decode v, op with
    | Some z, GoPos => Some v
    | Some z, GoNeg => Some (integer_literal (-z))
    | _, _ => None end
  | _ => None
  end.

Definition typed_conversion source target (v : @val field_syntax) : option val :=
  match scalar_type source, scalar_type target with
  | Some PointerKind, Some PointerKind =>
    if decide (source = target) then scalar_conversion PointerKind PointerKind v else None
  | Some source_kind, Some target_kind => scalar_conversion source_kind target_kind v
  | _, _ => None
  end.

Definition equality_values k (x y : @val field_syntax) : option (@val field_syntax) :=
  match k with
  | Bytes => match decode String x, decode String y with
    | Some x, Some y => Some (encode Bool (bool_decide (x = y))) | _, _ => None end
  | Boolean => match decode Bool x, decode Bool y with
    | Some x, Some y => Some (encode Bool (bool_decide (x = y))) | _, _ => None end
  | _ => None end.

Definition byte_binary op (x y : @val field_syntax) : option (@val field_syntax) :=
  match decode Uint8 x, decode Uint8 y, op with
  | Some x, Some y, GoAnd => Some (encode Uint8 (word.and x y))
  | _, _, _ => None
  end.

Definition pure_instruction (op : go_instruction) (arg : @val field_syntax) : option val :=
  match op with
  | GoZeroVal t => match scalar_type t, decode Unit arg with
    | Some k, Some _ => Some (zero_scalar k) | _, _ => None end
  | Convert source target => typed_conversion source target arg
  | GoUnOp op t => match scalar_type t with
    | Some k => scalar_unary k op arg | None => None end
  | GoOp op t => match scalar_type t, arg with
    | Some U64, PairV x y => decoded_binary false op x y
    | Some I64, PairV x y => decoded_binary true op x y
    | Some U8, PairV x y => byte_binary op x y
    | Some k, PairV x y => match op with GoEquals => equality_values k x y | _ => None end
    | _, _ => None end
  | _ => None
  end.

Lemma incompatible_pointer_cast_rejected :
  pure_instruction (Convert (go.PointerType go.uint64) (go.PointerType go.uint8))
    (encode Pointer (Loc 1 0)) = None.
Proof. reflexivity. Qed.

Lemma unary_preserves_type k op v result :
  scalar_unary k op v = Some result -> scalar_matches k result = true.
Proof.
  destruct k, op; cbn [scalar_unary]; try discriminate;
    repeat match goal with
    | |- context [decode ?t ?v] => destruct (decode t v) eqn:?
    | |- context [integer_decode ?v] => destruct (integer_decode v) eqn:?
    end; try discriminate; intros Heq; inversion Heq; subst result;
    try reflexivity; cbn [scalar_matches];
    repeat match goal with H : ?x = Some _ |- context [?x] => rewrite H end;
    reflexivity.
Qed.

Lemma conversion_instruction_preserves_type source target v result k :
  scalar_type target = Some k -> pure_instruction (Convert source target) v = Some result ->
  scalar_matches k result = true.
Proof.
  intros H. change (typed_conversion source target v = Some result -> scalar_matches k result = true).
  unfold typed_conversion. rewrite H.
  destruct (scalar_type source) as [s|]; [|discriminate].
  destruct s, k; try apply conversion_preserves_type.
  destruct (decide (source = target)); [apply conversion_preserves_type|discriminate].
Qed.

Lemma distinct_pointer_conversion_rejected s t v :
  go.PointerType s ≠ go.PointerType t ->
  pure_instruction (Convert (go.PointerType s) (go.PointerType t)) v = None.
Proof.
  intros H. cbn [pure_instruction typed_conversion scalar_type].
  rewrite decide_False; [reflexivity|exact H].
Qed.

Lemma string_equality x y :
  pure_instruction (GoOp GoEquals go.string) (PairV (encode String x) (encode String y)) =
  Some (encode Bool (bool_decide (x = y))).
Proof. reflexivity. Qed.

Lemma memory_is_not_pure t v : pure_instruction (GoLoad t) v = None /\
  pure_instruction (GoStore t) v = None /\ pure_instruction (GoAlloc t) v = None.
Proof. repeat split; reflexivity. Qed.

(* A partial pure instruction fragment. Memory, full Go execution, and native
   source correspondence are separate required obligations. *)
