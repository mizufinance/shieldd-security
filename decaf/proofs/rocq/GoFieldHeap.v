From Perennial.goose_lang Require Import lang.
From Stdlib Require Import List ZArith Lia.
Require Import GoFieldEncoding GoFieldSyntax.
Import ListNotations.

Definition field_heap := list (list (@val field_syntax)).
Definition read_cell (h : field_heap) block offset :=
  match nth_error h block with Some cells => nth_error cells offset | None => None end.
Definition write_cell (h : field_heap) block offset (value : @val field_syntax) : option field_heap :=
  match nth_error h block with
  | Some cells => match nth_error cells offset with
    | Some _ => Some (replace_at block (replace_at offset value cells) h)
    | None => None end
  | None => None end.

Definition address_indices (l : loc) : option (nat * nat) :=
  if decide (0 < loc_car l /\ 0 <= loc_off l) then
    Some (Z.to_nat (loc_car l - 1), Z.to_nat (loc_off l)) else None.
Definition read_address h l := match address_indices l with
  | Some (block, offset) => read_cell h block offset | None => None end.
Definition write_address h l value := match address_indices l with
  | Some (block, offset) => write_cell h block offset value | None => None end.
Definition allocate_cell (h : field_heap) (value : @val field_syntax) :=
  (Loc (Z.of_nat (length h) + 1) 0, h ++ [[value]]).

Lemma lookup_bound {A : Type} (xs : list A) i x : nth_error xs i = Some x -> (i < length xs)%nat.
Proof. intros H. apply nth_error_Some. rewrite H. discriminate. Qed.

Lemma write_read_same h block offset value h' :
  write_cell h block offset value = Some h' -> read_cell h' block offset = Some value.
Proof.
  unfold write_cell. destruct (nth_error h block) as [cells|] eqn:HB; [|discriminate].
  destruct (nth_error cells offset) as [old|] eqn:HO; [|discriminate].
  intros [= <-]. unfold read_cell.
  rewrite replace_here; [|eapply lookup_bound; exact HB].
  apply replace_here. eapply lookup_bound; exact HO.
Qed.

Lemma write_other_block h block offset value h' other index : block ≠ other ->
  write_cell h block offset value = Some h' -> read_cell h' other index = read_cell h other index.
Proof.
  intros Hne. unfold write_cell. destruct (nth_error h block) as [cells|]; [|discriminate].
  destruct (nth_error cells offset); [|discriminate]. intros [= <-].
  unfold read_cell. rewrite replace_elsewhere; [reflexivity|exact Hne].
Qed.

Lemma write_other_offset h block offset value h' other : offset ≠ other ->
  write_cell h block offset value = Some h' -> read_cell h' block other = read_cell h block other.
Proof.
  intros Hne. unfold write_cell. destruct (nth_error h block) as [cells|] eqn:HB; [|discriminate].
  destruct (nth_error cells offset); [|discriminate]. intros [= <-].
  unfold read_cell. rewrite replace_here; [|eapply lookup_bound; exact HB].
  rewrite HB. apply replace_elsewhere. exact Hne.
Qed.

Lemma null_read_rejected h : read_address h null = None.
Proof. reflexivity. Qed.
Lemma null_write_rejected h value : write_address h null value = None.
Proof. reflexivity. Qed.

Lemma allocation_address h value :
  address_indices (fst (allocate_cell h value)) = Some (length h, 0%nat).
Proof.
  unfold allocate_cell, address_indices. cbn.
  rewrite decide_True; [|lia].
  replace (Z.of_nat (length h) + 1 - 1) with (Z.of_nat (length h)) by lia.
  now rewrite Nat2Z.id.
Qed.

Lemma allocation_read h value :
  read_address (snd (allocate_cell h value)) (fst (allocate_cell h value)) = Some value.
Proof.
  unfold read_address. rewrite allocation_address.
  change (read_cell (h ++ [[value]]) (length h) 0 = Some value).
  unfold read_cell. rewrite nth_error_app2; [|lia].
  rewrite Nat.sub_diag. reflexivity.
Qed.

(* A finite abstract block heap. This is not yet connected to native addresses,
   allocation behavior, the Goose transition system, or field-body execution. *)
