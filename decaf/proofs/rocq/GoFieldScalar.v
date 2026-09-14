From New.golang Require Import defn.
From Stdlib Require Import Lia.
Require Import GoFieldEncoding GoFieldInteger GoFieldSyntax.

Inductive scalar_result := WordResult (w : w64) | BoolResult (b : bool).

Definition word_binary (signed : bool) (op : go_operator) (x y : w64) : option scalar_result :=
  let number := if signed then word.signed else word.unsigned in
  match op with
  | GoEquals => Some (BoolResult (bool_decide (x = y)))
  | GoLt => Some (BoolResult (bool_decide (number x < number y)))
  | GoLe => Some (BoolResult (bool_decide (number x <= number y)))
  | GoGt => Some (BoolResult (bool_decide (number y < number x)))
  | GoGe => Some (BoolResult (bool_decide (number y <= number x)))
  | GoPlus => Some (WordResult (word.add x y))
  | GoSub => Some (WordResult (word.sub x y))
  | GoMul => Some (WordResult (word.mul x y))
  | GoAnd => Some (WordResult (word.and x y))
  | GoOr => Some (WordResult (word.or x y))
  | GoXor => Some (WordResult (word.xor x y))
  | GoBitClear => Some (WordResult (word.and x (word.not y)))
  | GoShiftl => if decide (word.unsigned y < 64) then Some (WordResult (word.slu x y)) else None
  | GoShiftr => if decide (word.unsigned y < 64) then
      Some (WordResult ((if signed then word.srs else word.sru) x y)) else None
  | GoDiv | GoRemainder => None
  end.

Definition result_value (r : scalar_result) : @val field_syntax :=
  match r with WordResult w => encode Uint64 w | BoolResult b => encode Bool b end.

Definition decoded_binary signed op (a b : @val field_syntax) : option val :=
  match decode Uint64 a, decode Uint64 b with
  | Some x, Some y => option_map result_value (word_binary signed op x y)
  | _, _ => None
  end.

Lemma binary_decoding signed op x y :
  decoded_binary signed op (encode Uint64 x) (encode Uint64 y) =
    option_map result_value (word_binary signed op x y).
Proof. reflexivity. Qed.

Lemma binary_progress signed op x y : op ≠ GoDiv -> op ≠ GoRemainder ->
  (op = GoShiftl \/ op = GoShiftr -> word.unsigned y < 64) ->
  exists result, word_binary signed op x y = Some result.
Proof.
  destruct op; intros HD HR HS; cbn; try (eexists; reflexivity); try congruence.
  all: rewrite decide_True; [eexists; reflexivity|apply HS; auto].
Qed.

Lemma unsupported_shifts_rejected signed x y : 64 <= word.unsigned y ->
  word_binary signed GoShiftl x y = None /\ word_binary signed GoShiftr x y = None.
Proof.
  intros H. cbn. destruct (decide (word.unsigned y < 64)); [lia|]. split; reflexivity.
Qed.

Lemma result_typed r :
  (exists w, decode Uint64 (result_value r) = Some w) \/
  (exists b, decode Bool (result_value r) = Some b).
Proof. destruct r; [left|right]; eexists; reflexivity. Qed.

Lemma tagged_integer_is_not_pointer z :
  @decode field_syntax Pointer (integer_literal z) = None.
Proof. reflexivity. Qed.

(* This executable scalar fragment is not yet a complete instruction model,
   native refinement, or an execution proof for an extracted field body.
   Shift counts outside [0,64) are unsupported here, including valid large Go
   shifts; callers must prove the reached counts are inside this domain. *)
