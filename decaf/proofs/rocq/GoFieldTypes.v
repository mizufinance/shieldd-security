From New.golang Require Import defn.
Require Import GoFieldEncoding GoFieldInteger GoFieldSyntax GoFullSpecialization.

Inductive scalar_kind := U64 | I64 | U8 | Boolean | Bytes | Integer | PointerKind.
Definition scalar_kind_eq_dec (x y : scalar_kind) : {x = y} + {x ≠ y}.
Proof. decide equality. Defined.

Definition scalar_type (t : go.type) : option scalar_kind :=
  match t with
  | go.PointerType _ => Some PointerKind
  | _ =>
    if decide (t = go.uint64 \/ t = go.uint \/ t = literal_fiat.FqUint1 \/ t = literal_fiat.FrUint1) then Some U64 else
    if decide (t = go.int64 \/ t = go.int \/ t = literal_fiat.FqInt1 \/ t = literal_fiat.FrInt1) then Some I64 else
    if decide (t = go.uint8) then Some U8 else
    if decide (t = go.bool) then Some Boolean else
    if decide (t = go.string) then Some Bytes else
    if decide (t = go.untyped_int) then Some Integer else None
  end.

Definition scalar_matches k (v : @val field_syntax) : bool :=
  match k with
  | U64 | I64 => match decode Uint64 v with Some _ => true | None => false end
  | U8 => match decode Uint8 v with Some _ => true | None => false end
  | Boolean => match decode Bool v with Some _ => true | None => false end
  | Bytes => match decode String v with Some _ => true | None => false end
  | PointerKind => match decode Pointer v with Some _ => true | None => false end
  | Integer => match integer_decode v with Some _ => true | None => false end
  end.

Definition zero_scalar k : @val field_syntax :=
  match k with
  | U64 | I64 => encode Uint64 (W64 0)
  | U8 => encode Uint8 (W8 0)
  | Boolean => encode Bool false
  | Bytes => encode String []
  | PointerKind => encode Pointer null
  | Integer => integer_literal 0
  end.

Definition constant_fits k (z : Z) : Prop :=
  match k with
  | U64 => 0 <= z < 2^64
  | I64 => -(2^63) <= z < 2^63
  | U8 => 0 <= z < 2^8
  | _ => False
  end.
Global Instance constant_fits_dec k z : Decision (constant_fits k z).
Proof. destruct k; unfold constant_fits; apply _. Defined.

Definition scalar_conversion from to (v : @val field_syntax) : option val :=
  if scalar_matches from v then
    if scalar_kind_eq_dec from to then Some v else
    match from, to with
    | U64, I64 | I64, U64 => Some v
    | U8, U64 | U8, I64 =>
        match decode Uint8 v with Some x => Some (encode Uint64 (W64 (word.unsigned x))) | None => None end
    | U64, U8 | I64, U8 =>
        match decode Uint64 v with Some x => Some (encode Uint8 (W8 (word.unsigned x))) | None => None end
    | Integer, U64 | Integer, I64 =>
        match integer_decode v with Some z =>
          if decide (constant_fits to z) then Some (encode Uint64 (W64 z)) else None
          | None => None end
    | Integer, U8 =>
        match integer_decode v with Some z =>
          if decide (constant_fits U8 z) then Some (encode Uint8 (W8 z)) else None
          | None => None end
    | _, _ => None
    end
  else None.

Lemma zero_typed k : scalar_matches k (zero_scalar k) = true.
Proof. destruct k; reflexivity. Qed.

Lemma same_type_conversion k v : scalar_matches k v = true -> scalar_conversion k k v = Some v.
Proof. intros H. unfold scalar_conversion. rewrite H. destruct (scalar_kind_eq_dec k k); congruence. Qed.

Lemma integer_to_word z : constant_fits U64 z ->
  scalar_conversion Integer U64 (integer_literal z) = Some (encode Uint64 (W64 z)).
Proof.
  intros H. change ((if decide (constant_fits U64 z) then Some (@encode field_syntax Uint64 (W64 z)) else None) = Some (@encode field_syntax Uint64 (W64 z))).
  rewrite decide_True; [reflexivity|exact H].
Qed.
Lemma integer_to_pointer_rejected z : scalar_conversion Integer PointerKind (integer_literal z) = None.
Proof. reflexivity. Qed.

Lemma conversion_preserves_type from to v result :
  scalar_conversion from to v = Some result -> scalar_matches to result = true.
Proof.
  unfold scalar_conversion. destruct (scalar_matches from v) eqn:H; [|discriminate].
  destruct (scalar_kind_eq_dec from to) as [->|Hne].
  - intros [= <-]. exact H.
  - destruct from, to; try contradiction; try discriminate;
      repeat match goal with
      | |- context [decode ?t ?v] => destruct (decode t v) eqn:?
      | |- context [integer_decode ?v] => destruct (integer_decode v) eqn:?
      | |- context [decide ?P] => destruct (decide P)
      end; try discriminate; intros Heq; inversion Heq; subst result; try reflexivity; exact H.
Qed.

Lemma overflowing_byte_constant_rejected :
  scalar_conversion Integer U8 (integer_literal 256) = None.
Proof. vm_compute. reflexivity. Qed.
Lemma negative_unsigned_constant_rejected :
  scalar_conversion Integer U64 (integer_literal (-1)) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma mismatched_input_rejected from to v : scalar_matches from v = false ->
  scalar_conversion from to v = None.
Proof. intros H. unfold scalar_conversion. rewrite H. reflexivity. Qed.

Lemma fq_unsigned_type : scalar_type literal_fiat.FqUint1 = Some U64.
Proof. vm_compute. reflexivity. Qed.
Lemma fr_signed_type : scalar_type literal_fiat.FrInt1 = Some I64.
Proof. vm_compute. reflexivity. Qed.

