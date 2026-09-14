From New.golang Require Import defn.
From Stdlib Require Import Lia.
Require Import GoFieldEncoding GoFieldSyntax.

Inductive reference_result := Reference (l : loc) | NilReference | IndexOutOfRange.

Definition checked_reference (length : Z) (base : loc) (index : w64) :=
  if decide (0 <= word.signed index < length) then
    if decide (base = null) then NilReference
    else Reference (go.array_offset base (word.signed index))
  else IndexOutOfRange.

Definition decode_reference length (v : @val field_syntax) : option reference_result :=
  match v with
  | PairV base index => match decode Pointer base, decode Uint64 index with
    | Some base, Some index => Some (checked_reference length base index)
    | _, _ => None end
  | _ => None end.

Lemma reference_progress length base index :
  (exists l, checked_reference length base index = Reference l) \/
  checked_reference length base index = NilReference \/
  checked_reference length base index = IndexOutOfRange.
Proof.
  unfold checked_reference. destruct (decide (0 <= word.signed index < length)).
  - destruct (decide (base = null)); [right; left|left; eexists]; reflexivity.
  - right; right; reflexivity.
Qed.

Lemma reference_valid length base index :
  0 <= word.signed index < length -> base ≠ null ->
  checked_reference length base index = Reference (go.array_offset base (word.signed index)).
Proof. intros HB HN. unfold checked_reference. rewrite decide_True; [|exact HB]. rewrite decide_False; [reflexivity|exact HN]. Qed.

Lemma reference_bounds_checked length base index l :
  checked_reference length base index = Reference l ->
  0 <= word.signed index < length /\ base ≠ null.
Proof.
  unfold checked_reference. destruct (decide (0 <= word.signed index < length)); [|discriminate].
  destruct (decide (base = null)); [discriminate|auto].
Qed.

Lemma reference_matches_cells length base index :
  0 <= word.signed index < length -> addr_base base ≠ null ->
  checked_reference length base index = Reference (loc_add base (word.signed index)).
Proof.
  intros HB HA. assert (base ≠ null) as HN by (intros ->; apply HA; reflexivity).
  rewrite (reference_valid _ _ _ HB HN). unfold go.array_offset.
  rewrite decide_False; [reflexivity|exact HA].
Qed.

Lemma negative_index_rejected length base index : word.signed index < 0 ->
  checked_reference length base index = IndexOutOfRange.
Proof. intros H. unfold checked_reference. rewrite decide_False; [reflexivity|lia]. Qed.

Lemma tagged_reference_rejected length z index :
  decode_reference length (PairV (InjLV (LitV (LitLoc (Loc z 0)))) (encode Uint64 index)) = None.
Proof. reflexivity. Qed.

(* Addresses here are abstract Goose heap cells. Native byte addressing,
   allocation validity, and execution correspondence remain to be proved. *)
