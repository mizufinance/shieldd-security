From New.golang Require Import defn.
From Stdlib Require Import List ZArith Lia.
Require Import GoFieldEncoding GoFieldInteger GoFieldSyntax GoFieldTypes GoFieldHeap.
Import ListNotations.

Lemma replace_after_prefix {A : Type} (prefix xs : list A) i value :
  replace_at (length prefix + i) value (prefix ++ xs) = prefix ++ replace_at i value xs.
Proof. induction prefix; cbn; [reflexivity|now rewrite IHprefix]. Qed.

Lemma read_after_prefix (prefix h : field_heap) block offset :
  read_cell (prefix ++ h) (length prefix + block) offset = read_cell h block offset.
Proof.
  unfold read_cell. rewrite nth_error_app2; [|lia].
  replace (length prefix + block - length prefix)%nat with block by lia. reflexivity.
Qed.

Lemma write_after_prefix (prefix h : field_heap) block offset value :
  write_cell (prefix ++ h) (length prefix + block) offset value =
  option_map (fun h' => prefix ++ h') (write_cell h block offset value).
Proof.
  unfold write_cell. rewrite nth_error_app2; [|lia].
  replace (length prefix + block - length prefix)%nat with block by lia.
  destruct (nth_error h block) as [cells|]; [|reflexivity].
  destruct (nth_error cells offset); [|reflexivity].
  cbn. now rewrite replace_after_prefix.
Qed.

Lemma read_mapped (f : @val field_syntax -> @val field_syntax) h block offset :
  read_cell (map (map f) h) block offset = option_map f (read_cell h block offset).
Proof.
  unfold read_cell. rewrite nth_error_map.
  destruct (nth_error h block); [cbn; apply nth_error_map|reflexivity].
Qed.

Definition relocate_pointer (k : nat) (l : loc) : loc :=
  if decide (0 < loc_car l) then Loc (loc_car l + Z.of_nat k) (loc_off l) else l.

Lemma pointer_prefix_control : relocate_pointer 1 (Loc 1 0) = Loc 2 0.
Proof. reflexivity. Qed.

Lemma address_indices_shift k l :
  address_indices (relocate_pointer k l) =
  option_map (fun '(block, offset) => ((k + block)%nat, offset)) (address_indices l).
Proof.
  destruct l as [base offset]. unfold relocate_pointer, address_indices. cbn.
  destruct (decide (0 < base)) as [HB|HB].
  - cbn. destruct (decide (0 < base /\ 0 <= offset)) as [HO|HO].
    + rewrite decide_True; [|lia]. cbn.
      replace (base + Z.of_nat k - 1) with (Z.of_nat k + (base - 1)) by lia.
      rewrite Z2Nat.inj_add; [|lia|lia]. rewrite Nat2Z.id. reflexivity.
    + rewrite decide_False; [reflexivity|lia].
  - cbn. destruct (decide (0 < base /\ 0 <= offset)); [lia|reflexivity].
Qed.

Lemma relocated_read prefix h l :
  read_address (prefix ++ h) (relocate_pointer (length prefix) l) = read_address h l.
Proof.
  unfold read_address. rewrite address_indices_shift.
  destruct (address_indices l) as [[block offset]|]; [apply read_after_prefix|reflexivity].
Qed.

Lemma relocated_write prefix h l value :
  write_address (prefix ++ h) (relocate_pointer (length prefix) l) value =
  option_map (fun h' => prefix ++ h') (write_address h l value).
Proof.
  unfold write_address. rewrite address_indices_shift.
  destruct (address_indices l) as [[block offset]|]; [apply write_after_prefix|reflexivity].
Qed.

Fixpoint relocate_expr (k : nat) (e : @expr field_syntax) : expr :=
  match e with
  | Val v => Val (relocate_value k v)
  | Var x => Var x
  | Rec f binder body => Rec f binder (relocate_expr k body)
  | App f x => App (relocate_expr k f) (relocate_expr k x)
  | Pair x y => Pair (relocate_expr k x) (relocate_expr k y)
  | If c yes no => If (relocate_expr k c) (relocate_expr k yes) (relocate_expr k no)
  | Fst x => Fst (relocate_expr k x)
  | Snd x => Snd (relocate_expr k x)
  | _ => e end
with relocate_value (k : nat) (v : @val field_syntax) : val :=
  match v with
  | LitV (LitLoc l) => LitV (LitLoc (relocate_pointer k l))
  | RecV f binder body => RecV f binder (relocate_expr k body)
  | PairV x y => PairV (relocate_value k x) (relocate_value k y)
  | _ => v end.

Lemma tagged_integer_frame_control : relocate_value 1 (integer_literal 1) = integer_literal 1.
Proof. reflexivity. Qed.

Fixpoint simple_expr (e : @expr field_syntax) : bool :=
  match e with
  | Val _ | Var _ => true
  | Rec _ _ body => simple_expr body
  | App f x | Pair f x => simple_expr f && simple_expr x
  | If c yes no => simple_expr c && simple_expr yes && simple_expr no
  | Fst x | Snd x => simple_expr x
  | _ => false end.

Lemma scalar_matches_relocated k kind v :
  scalar_matches kind (relocate_value k v) = scalar_matches kind v.
Proof. destruct kind, v; try reflexivity; destruct l; reflexivity. Qed.

Lemma pointer_decode_relocated k v :
  decode Pointer (relocate_value k v) = option_map (relocate_pointer k) (decode Pointer v).
Proof. destruct v; try reflexivity; destruct l; reflexivity. Qed.

Lemma integer_relocation_fixed k z : relocate_value k (integer_literal z) = integer_literal z.
Proof. reflexivity. Qed.

Lemma relocate_substitution k x v e : simple_expr e = true ->
  relocate_expr k (subst x v e) = subst x (relocate_value k v) (relocate_expr k e).
Proof.
  induction e; intros H; cbn [simple_expr] in H; try discriminate; cbn [subst relocate_expr].
  - reflexivity.
  - destruct (decide (x = x0)); reflexivity.
  - destruct (decide (BNamed x ≠ f /\ BNamed x ≠ x0)); cbn [relocate_expr]; [rewrite IHe; [reflexivity|exact H]|reflexivity].
  - apply andb_true_iff in H as [H1 H2]. rewrite (IHe1 H1) (IHe2 H2). reflexivity.
  - apply andb_true_iff in H as [H12 H3]. apply andb_true_iff in H12 as [H1 H2].
    rewrite (IHe1 H1) (IHe2 H2) (IHe3 H3). reflexivity.
  - apply andb_true_iff in H as [H1 H2]. rewrite (IHe1 H1) (IHe2 H2). reflexivity.
  - rewrite IHe; [reflexivity|exact H].
  - rewrite IHe; [reflexivity|exact H].
Qed.

Lemma relocate_substitution_binder k binder v e : simple_expr e = true ->
  relocate_expr k (subst' binder v e) = subst' binder (relocate_value k v) (relocate_expr k e).
Proof. destruct binder; [reflexivity|apply relocate_substitution]. Qed.

Lemma map_replace {A B : Type} (f : A -> B) xs i value :
  map f (replace_at i value xs) = replace_at i (f value) (map f xs).
Proof. revert i. induction xs; intros [|i]; cbn; try reflexivity. now rewrite IHxs. Qed.

Lemma write_mapped (f : @val field_syntax -> @val field_syntax) h block offset value :
  write_cell (map (map f) h) block offset (f value) =
  option_map (map (map f)) (write_cell h block offset value).
Proof.
  unfold write_cell. rewrite nth_error_map.
  destruct (nth_error h block) as [cells|]; [|reflexivity]. cbn.
  rewrite nth_error_map. destruct (nth_error cells offset); [|reflexivity].
  cbn. now rewrite !map_replace.
Qed.

Definition relocate_heap k h := map (map (relocate_value k)) h.
Definition frame_heap prefix h := prefix ++ relocate_heap (length prefix) h.

Lemma framed_read prefix h l :
  read_address (frame_heap prefix h) (relocate_pointer (length prefix) l) =
  option_map (relocate_value (length prefix)) (read_address h l).
Proof.
  unfold frame_heap. rewrite relocated_read.
  unfold read_address. destruct (address_indices l) as [[block offset]|];
    [apply read_mapped|reflexivity].
Qed.

Lemma framed_write prefix h l value :
  write_address (frame_heap prefix h) (relocate_pointer (length prefix) l)
    (relocate_value (length prefix) value) =
  option_map (frame_heap prefix) (write_address h l value).
Proof.
  unfold frame_heap. rewrite relocated_write.
  unfold write_address. destruct (address_indices l) as [[block offset]|]; [|reflexivity].
  unfold relocate_heap. rewrite write_mapped.
  destruct (write_cell h block offset value); reflexivity.
Qed.

Lemma framed_allocation prefix h value :
  allocate_cell (frame_heap prefix h) (relocate_value (length prefix) value) =
  let '(l, h') := allocate_cell h value in
    (relocate_pointer (length prefix) l, frame_heap prefix h').
Proof.
  unfold allocate_cell, frame_heap, relocate_heap, relocate_pointer. cbn.
  rewrite decide_True; [|lia].
  rewrite app_length !map_length Nat2Z.inj_add map_app. cbn.
  rewrite app_assoc.
  replace (Z.of_nat (length prefix) + Z.of_nat (length h) + 1)
    with (Z.of_nat (length h) + 1 + Z.of_nat (length prefix)) by lia.
  reflexivity.
Qed.

(* Conditional framing of the explicit field evaluator only. The fragment
   predicate admits resolver names that may fail to resolve. These proofs
   do not assert progress, native adequacy, or allocation/resource bounds.
   Arrays and sum payloads are not recursively relocated. *)
