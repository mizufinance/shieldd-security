From New.golang Require Import defn.
From Stdlib Require Import List ZArith Lia.
Require Import GoFieldEncoding GoFieldInteger GoFieldSyntax GoFieldTypes GoFieldScalar GoFieldPure GoFieldReference GoFieldHeap GoFieldEval GoLiteralDispatch GoFieldHeapFrame.
Import ListNotations.

Definition frame_result prefix (result : @val field_syntax * field_heap) :=
  let '(v, h) := result in (relocate_value (length prefix) v, frame_heap prefix h).

Lemma allocation_instruction_frame prefix h t arg :
  instruction (GoAlloc t) (relocate_value (length prefix) arg) (frame_heap prefix h) =
  option_map (frame_result prefix) (instruction (GoAlloc t) arg h).
Proof.
  cbn [instruction]. destruct (scalar_type t) as [kind|]; [|reflexivity].
  rewrite scalar_matches_relocated. destruct (scalar_matches kind arg); [|reflexivity].
  rewrite framed_allocation. destruct (allocate_cell h arg). reflexivity.
Qed.

Lemma load_instruction_frame prefix h t arg :
  instruction (GoLoad t) (relocate_value (length prefix) arg) (frame_heap prefix h) =
  option_map (frame_result prefix) (instruction (GoLoad t) arg h).
Proof.
  cbn [instruction]. rewrite pointer_decode_relocated.
  destruct (scalar_type t) as [kind|]; [|reflexivity].
  destruct (decode Pointer arg) as [pointer|]; [|reflexivity]. cbn.
  rewrite framed_read. destruct (read_address h pointer) as [value|]; [|reflexivity]. cbn.
  rewrite scalar_matches_relocated. destruct (scalar_matches kind value); reflexivity.
Qed.

Lemma store_pair_instruction_frame prefix h t pointer value :
  instruction (GoStore t) (relocate_value (length prefix) (PairV pointer value)) (frame_heap prefix h) =
  option_map (frame_result prefix) (instruction (GoStore t) (PairV pointer value) h).
Proof.
  cbn [instruction relocate_value]. destruct (scalar_type t) as [kind|]; [|reflexivity].
  rewrite pointer_decode_relocated. destruct (decode Pointer pointer) as [address|]; [|reflexivity]. cbn.
  rewrite scalar_matches_relocated. destruct (scalar_matches kind value); [|reflexivity].
  rewrite framed_read. destruct (read_address h address) as [old|]; [|reflexivity]. cbn.
  rewrite scalar_matches_relocated. destruct (scalar_matches kind old); [|reflexivity].
  rewrite framed_write. destruct (write_address h address value); reflexivity.
Qed.

Lemma nonpointer_decode_relocated k r v : r ≠ Pointer ->
  (forall n element, r ≠ Array n element) ->
  decode r (relocate_value k v) = decode r v.
Proof.
  destruct r; intros HP HA; try contradiction.
  all: try (exfalso; eapply HA; reflexivity).
  all: destruct v; try reflexivity; destruct l; reflexivity.
Qed.

Lemma integer_decode_relocated k v : integer_decode (relocate_value k v) = integer_decode v.
Proof. destruct v; try reflexivity; destruct l; reflexivity. Qed.

Lemma zero_relocated k kind : relocate_value k (zero_scalar kind) = zero_scalar kind.
Proof. destruct kind; reflexivity. Qed.

Lemma conversion_relocated k source target v :
  scalar_conversion source target (relocate_value k v) =
  option_map (relocate_value k) (scalar_conversion source target v).
Proof.
  unfold scalar_conversion. rewrite scalar_matches_relocated.
  destruct (scalar_matches source v); [|reflexivity].
  destruct (scalar_kind_eq_dec source target); [reflexivity|].
  destruct source, target; try reflexivity;
    rewrite ?nonpointer_decode_relocated ?integer_decode_relocated;
    try discriminate;
    repeat match goal with
    | |- context [decode ?t ?v] => destruct (decode t v)
    | |- context [integer_decode ?v] => destruct (integer_decode v)
    | |- context [decide ?P] => destruct (decide P)
    end; reflexivity.
Qed.

Lemma typed_conversion_relocated k source target v :
  typed_conversion source target (relocate_value k v) =
  option_map (relocate_value k) (typed_conversion source target v).
Proof.
  unfold typed_conversion.
  destruct (scalar_type source) as [s|]; [|reflexivity].
  destruct (scalar_type target) as [t|]; [|destruct s; reflexivity].
  destruct s, t; try apply conversion_relocated.
  destruct (decide (source = target)); [apply conversion_relocated|reflexivity].
Qed.

Lemma unary_relocated k kind op v :
  scalar_unary kind op (relocate_value k v) =
  option_map (relocate_value k) (scalar_unary kind op v).
Proof.
  destruct kind, op; cbn [scalar_unary]; try reflexivity;
    rewrite ?nonpointer_decode_relocated ?integer_decode_relocated; try discriminate;
    repeat match goal with
    | |- context [decode ?t ?v] => destruct (decode t v)
    | |- context [integer_decode ?v] => destruct (integer_decode v)
    end; reflexivity.
Qed.

Lemma binary_relocated k signed op x y :
  decoded_binary signed op (relocate_value k x) (relocate_value k y) =
  option_map (relocate_value k) (decoded_binary signed op x y).
Proof.
  unfold decoded_binary.
  rewrite !nonpointer_decode_relocated; try discriminate.
  destruct (decode Uint64 x), (decode Uint64 y); try reflexivity.
  destruct (word_binary signed op c c0) as [result|]; [destruct result|]; reflexivity.
Qed.

Lemma byte_binary_relocated k op x y :
  byte_binary op (relocate_value k x) (relocate_value k y) =
  option_map (relocate_value k) (byte_binary op x y).
Proof.
  unfold byte_binary. rewrite !nonpointer_decode_relocated; try discriminate.
  destruct (decode Uint8 x), (decode Uint8 y), op; reflexivity.
Qed.

Lemma equality_relocated k kind x y :
  equality_values kind (relocate_value k x) (relocate_value k y) =
  option_map (relocate_value k) (equality_values kind x y).
Proof.
  destruct kind; cbn [equality_values]; try reflexivity;
    rewrite !nonpointer_decode_relocated; try discriminate;
    repeat match goal with |- context [decode ?t ?v] => destruct (decode t v) end;
    reflexivity.
Qed.

Lemma pure_instruction_relocated k op arg :
  pure_instruction op (relocate_value k arg) =
  option_map (relocate_value k) (pure_instruction op arg).
Proof.
  destruct op; cbn [pure_instruction]; try reflexivity.
  all: try apply typed_conversion_relocated.
  all: try (destruct (scalar_type t) as [kind|]; [apply unary_relocated|reflexivity]).
  - destruct (scalar_type t) as [kind|]; [|reflexivity].
    destruct kind, arg; cbn [relocate_value]; try reflexivity;
      try apply binary_relocated; try apply byte_binary_relocated;
      try (destruct o; try reflexivity; apply equality_relocated);
      destruct l; reflexivity.
  - rewrite nonpointer_decode_relocated; [|discriminate|intros; discriminate].
    destruct (scalar_type t), (decode Unit arg); cbn; try reflexivity.
    now rewrite zero_relocated.
Qed.

Lemma relocated_null k l : relocate_pointer k l = null <-> l = null.
Proof.
  destruct l as [base offset]. unfold relocate_pointer. cbn.
  destruct (decide (0 < base)) as [HB|HB]; [|tauto].
  split; intros H; apply (f_equal loc_car) in H; cbn in H; lia.
Qed.

Lemma relocated_base_null k l :
  addr_base (relocate_pointer k l) = null <-> addr_base l = null.
Proof.
  destruct l as [base offset]. unfold relocate_pointer. cbn.
  destruct (decide (0 < base)) as [HB|HB]; [|tauto].
  split; intros H; apply (f_equal loc_car) in H; cbn in H; lia.
Qed.

Lemma relocated_offset k l offset :
  go.array_offset (relocate_pointer k l) offset = relocate_pointer k (go.array_offset l offset).
Proof.
  unfold go.array_offset.
  destruct (decide (addr_base l = null)) as [HN|HN].
  - rewrite decide_True; [reflexivity|apply relocated_base_null; exact HN].
  - rewrite decide_False; [|intros H; apply HN; apply relocated_base_null in H; exact H].
    destruct l as [base position]. unfold relocate_pointer, loc_add, addr_plus_off. cbn.
    destruct (decide (0 < base)); reflexivity.
Qed.

Definition relocate_reference k result :=
  match result with Reference l => Reference (relocate_pointer k l) | _ => result end.

Lemma checked_reference_relocated k n base index :
  checked_reference n (relocate_pointer k base) index =
  relocate_reference k (checked_reference n base index).
Proof.
  unfold checked_reference. destruct (decide (0 <= word.signed index < n)); [|reflexivity].
  destruct (decide (base = null)) as [HN|HN].
  - rewrite decide_True; [reflexivity|apply relocated_null; exact HN].
  - rewrite decide_False; [|intros H; apply HN; apply relocated_null in H; exact H].
    cbn. now rewrite relocated_offset.
Qed.

Lemma decode_reference_relocated k n arg :
  decode_reference n (relocate_value k arg) =
  option_map (relocate_reference k) (decode_reference n arg).
Proof.
  destruct arg; cbn [relocate_value decode_reference]; try reflexivity;
    try (destruct l; reflexivity).
  rewrite pointer_decode_relocated nonpointer_decode_relocated; try discriminate.
  destruct (decode Pointer arg1), (decode Uint64 arg2); cbn; try reflexivity.
  now rewrite checked_reference_relocated.
Qed.

Lemma function_body_relocated k id : relocate_value k (function_body id) = function_body id.
Proof. destruct id; reflexivity. Qed.

Lemma dispatch_relocated k name :
  option_map (relocate_value k) (dispatch name) = dispatch name.
Proof.
  unfold dispatch. destruct (resolve name) as [id|]; [|reflexivity]. cbn.
  now rewrite function_body_relocated.
Qed.

Lemma instruction_relocated prefix h op arg :
  instruction op (relocate_value (length prefix) arg) (frame_heap prefix h) =
  option_map (frame_result prefix) (instruction op arg h).
Proof.
  destruct op; try apply allocation_instruction_frame; try apply load_instruction_frame;
    cbn [instruction]; try (rewrite pure_instruction_relocated;
      destruct (pure_instruction _ arg); reflexivity).
  - destruct arg; try apply store_pair_instruction_frame;
      destruct (scalar_type t); try reflexivity; destruct l; reflexivity.
  - destruct type_args; [|reflexivity]. unfold dispatch.
    destruct (resolve f); [|reflexivity]. cbn [option_map frame_result].
    now rewrite function_body_relocated.
  - destruct t; try reflexivity.
    destruct (decide (t = go.uint64 \/ t = go.uint8)); [|reflexivity].
    rewrite decode_reference_relocated.
    destruct (decode_reference z arg) as [result|]; [destruct result|]; reflexivity.
Qed.

(* Conditional framing of the explicit field evaluator only. The fragment
   predicate admits resolver names that may fail to resolve. These proofs
   do not assert progress, native adequacy, or allocation/resource bounds.
   Arrays and sum payloads are not recursively relocated. *)
