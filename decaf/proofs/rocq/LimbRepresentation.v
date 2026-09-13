(* Shared integer representation facts. Native casts, shifts, array accesses and
   wrapper execution must be connected separately to these mathematical maps. *)
From Stdlib Require Import ZArith Lia List.
Import ListNotations.
Open Scope Z_scope.

Definition radix32 : Z := 4294967296.
Definition radix64 : Z := 18446744073709551616.
Definition canonical32 (x : Z) := 0 <= x < radix32.
Definition canonical64 (x : Z) := 0 <= x < radix64.
Definition split_word (x : Z) := [x mod radix32; x / radix32].
Definition split_words (xs : list Z) := flat_map split_word xs.
Definition join_word (lo hi : Z) := lo + radix32 * hi.
Fixpoint join_words (xs : list Z) :=
  match xs with lo :: hi :: rest => join_word lo hi :: join_words rest | _ => [] end.
Fixpoint value (radix : Z) (xs : list Z) :=
  match xs with [] => 0 | x :: rest => x + radix * value radix rest end.

Lemma radix_relation : radix64 = radix32 * radix32.
Proof. reflexivity. Qed.

Lemma split_reconstruct x : x mod radix32 + radix32 * (x / radix32) = x.
Proof.
  pose proof (Z.div_mod x radix32 ltac:(unfold radix32; lia)). lia.
Qed.

Theorem split_canonical x : canonical64 x -> Forall canonical32 (split_word x).
Proof.
  unfold canonical64, split_word, canonical32. intros Hx.
  constructor.
  - apply Z.mod_pos_bound. unfold radix32; lia.
  - constructor; [|constructor]. split.
    + apply Z.div_pos; unfold radix32, radix64 in *; lia.
    + apply Z.div_lt_upper_bound; unfold radix32, radix64 in *; lia.
Qed.

Theorem split_words_value xs : value radix32 (split_words xs) = value radix64 xs.
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  change (x mod radix32 + radix32 * (x / radix32 + radix32 * value radix32 (split_words xs))
          = x + radix64 * value radix64 xs).
  rewrite IH, radix_relation.
  pose proof (split_reconstruct x). nia.
Qed.

Theorem split_words_canonical xs :
  Forall canonical64 xs -> Forall canonical32 (split_words xs).
Proof.
  intros H. induction H; [constructor|].
  unfold split_words in *. cbn [flat_map].
  apply Forall_app. split; [now apply split_canonical|assumption].
Qed.

Theorem split_words_length xs : length (split_words xs) = (2 * length xs)%nat.
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  change (S (S (length (split_words xs))) = (2 * S (length xs))%nat).
  rewrite IH. lia.
Qed.

Theorem montgomery_radix_agreement : radix32 ^ 8 = radix64 ^ 4 /\ radix32 ^ 8 = 2 ^ 256.
Proof. split; reflexivity. Qed.

Theorem canonical_residue_preserved modulus xs :
  0 <= value radix64 xs < modulus ->
  0 <= value radix32 (split_words xs) < modulus.
Proof. now rewrite split_words_value. Qed.

Theorem join_canonical lo hi :
  canonical32 lo -> canonical32 hi -> canonical64 (join_word lo hi).
Proof. unfold canonical32, canonical64, join_word, radix32, radix64; lia. Qed.

Theorem join_split x : join_word (x mod radix32) (x / radix32) = x.
Proof. apply split_reconstruct. Qed.

Theorem split_join lo hi : canonical32 lo -> canonical32 hi ->
  split_word (join_word lo hi) = [lo; hi].
Proof.
  intros Hlo Hhi. unfold canonical32 in *.
  assert (Hm : join_word lo hi mod radix32 = lo).
  { symmetry. apply Z.mod_unique with (q := hi).
    - left; exact Hlo.
    - unfold join_word; ring. }
  assert (Hd : join_word lo hi / radix32 = hi).
  { symmetry. apply Z.div_unique with (r := lo).
    - left; exact Hlo.
    - unfold join_word; ring. }
  unfold split_word. now rewrite Hm, Hd.
Qed.

Theorem join_split_words xs : join_words (split_words xs) = xs.
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  change (join_word (x mod radix32) (x / radix32) :: join_words (split_words xs) = x :: xs).
  now rewrite join_split, IH.
Qed.

Theorem four_word_conversion xs : length xs = 4%nat -> Forall canonical64 xs ->
  length (split_words xs) = 8%nat /\ Forall canonical32 (split_words xs) /\
  value radix32 (split_words xs) = value radix64 xs /\ join_words (split_words xs) = xs.
Proof.
  intros Hlen Hcan. repeat split.
  - now rewrite split_words_length, Hlen.
  - now apply split_words_canonical.
  - apply split_words_value.
  - apply join_split_words.
Qed.

Theorem canonical_digits_unique radix xs ys :
  1 < radix -> length xs = length ys ->
  Forall (fun x => 0 <= x < radix) xs ->
  Forall (fun y => 0 <= y < radix) ys ->
  value radix xs = value radix ys -> xs = ys.
Proof.
  intros Hr Hlen Hxs Hys Hvalue.
  revert ys Hlen Hys Hvalue.
  induction Hxs as [|x xs Hx Hxs IH]; intros ys Hlen Hys Hvalue.
  - destruct ys; [reflexivity | cbn in Hlen; discriminate].
  - destruct ys as [|y ys]; [cbn in Hlen; discriminate|].
    inversion Hys as [|? ? Hy Hys']; subst; clear Hys.
    cbn [value] in Hvalue.
    assert (Hhead : x = y).
    { pose proof (f_equal (fun z => z mod radix) Hvalue) as Hmod.
      replace (radix * value radix xs) with (value radix xs * radix) in Hmod by ring.
      replace (radix * value radix ys) with (value radix ys * radix) in Hmod by ring.
      rewrite !Z.mod_add in Hmod by lia.
      rewrite (Z.mod_small x radix), (Z.mod_small y radix) in Hmod by assumption.
      exact Hmod. }
    subst y. f_equal. apply IH; [cbn in Hlen; lia | exact Hys' | nia].
Qed.

Theorem canonical_residue_digits_unique radix modulus xs ys :
  1 < radix -> length xs = length ys ->
  Forall (fun x => 0 <= x < radix) xs ->
  Forall (fun y => 0 <= y < radix) ys ->
  0 <= value radix xs < modulus -> 0 <= value radix ys < modulus ->
  value radix xs mod modulus = value radix ys mod modulus -> xs = ys.
Proof.
  intros Hr Hlen Hxs Hys Hx Hy Heq.
  apply canonical_digits_unique with (radix := radix); try assumption.
  now rewrite !Z.mod_small in Heq by assumption.
Qed.
