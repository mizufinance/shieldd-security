From Perennial.goose_lang Require Import lang.
From Stdlib Require Import List.
Import ListNotations.

(* A constructive, explicitly indexed value interface. It is not an instance
   of the existing universal GoGlobalContext and is not an execution model. *)
Inductive field_repr :=
| Unit | Bool | Uint8 | Uint64 | Int64 | Pointer | String
| Array (length : nat) (element : field_repr).

Fixpoint carrier (r : field_repr) : Type :=
  match r with
  | Unit => unit | Bool => bool | Uint8 => w8 | Uint64 | Int64 => w64
  | Pointer => loc | String => go_string | Array _ element => list (carrier element)
  end.

Fixpoint wellformed (r : field_repr) : carrier r -> Prop :=
  match r return carrier r -> Prop with
  | Array n element => fun xs => List.length xs = n /\ Forall (wellformed element) xs
  | _ => fun _ => True
  end.

Section encoding.
Context {ext : ffi_syntax}.

Fixpoint encode (r : field_repr) : carrier r -> val :=
  match r return carrier r -> val with
  | Unit => fun _ => LitV LitUnit
  | Bool => fun b => LitV (LitBool b)
  | Uint8 => fun w => LitV (LitByte w)
  | Uint64 | Int64 => fun w => LitV (LitInt w)
  | Pointer => fun l => LitV (LitLoc l)
  | String => fun s => LitV (LitString s)
  | Array _ element => fun xs => ArrayV (List.map (encode element) xs)
  end.

Lemma map_injective {A B : Type} (f : A -> B) :
  (forall x y, f x = f y -> x = y) ->
  forall xs ys, List.map f xs = List.map f ys -> xs = ys.
Proof.
  intros Hinj xs. induction xs as [|x xs IH]; intros ys H; destruct ys as [|y ys];
    cbn in H; try discriminate; first reflexivity.
  inversion H. f_equal; [apply Hinj; assumption|apply IH; assumption].
Qed.

Lemma encode_injective r : forall x y, encode r x = encode r y -> x = y.
Proof.
  induction r; intros x y H; cbn in H.
  - destruct x, y. reflexivity.
  - now inversion H.
  - now inversion H.
  - now inversion H.
  - now inversion H.
  - now inversion H.
  - now inversion H.
  - inversion H. apply (map_injective (encode r) IHr). assumption.
Qed.

Lemma array_length n element xs :
  wellformed (Array n element) xs ->
  exists values, encode (Array n element) xs = ArrayV values /\ List.length values = n.
Proof.
  intros [Hlen _]. exists (List.map (encode element) xs).
  split; [reflexivity|now rewrite List.length_map].
Qed.

Lemma four_words a b c d : wellformed (Array 4 Uint64) [a;b;c;d].
Proof. split; [reflexivity|repeat constructor]. Qed.
End encoding.

Fixpoint traverse {A B : Type} (f : A -> option B) (xs : list A) : option (list B) :=
  match xs with
  | [] => Some []
  | x :: xs => match f x, traverse f xs with
               | Some y, Some ys => Some (y :: ys)
               | _, _ => None
               end
  end.

Lemma traverse_map {A B : Type} (e : A -> B) (d : B -> option A) (P : A -> Prop) :
  (forall x, P x -> d (e x) = Some x) ->
  forall xs, Forall P xs -> traverse d (List.map e xs) = Some xs.
Proof.
  intros H xs Hxs. induction Hxs as [|x xs Hx Hxs IH]; cbn; first reflexivity.
  now rewrite (H x Hx) IH.
Qed.

Lemma traverse_sound {A B : Type} (e : A -> B) (d : B -> option A) (P : A -> Prop) :
  (forall v x, d v = Some x -> e x = v /\ P x) ->
  forall vs xs, traverse d vs = Some xs -> List.map e xs = vs /\ Forall P xs.
Proof.
  intros H vs. induction vs as [|v vs IH]; intros xs Hxs; cbn in Hxs.
  - inversion Hxs; subst. split; constructor.
  - destruct (d v) as [x|] eqn:Hx; try discriminate.
    destruct (traverse d vs) as [ys|] eqn:Hys; try discriminate.
    inversion Hxs; subst xs. destruct (H _ _ Hx) as [He HP].
    destruct (IH _ eq_refl) as [Hes HPs]. cbn. rewrite He Hes.
    split; [reflexivity|now constructor].
Qed.

Section decoding.
Context {ext : ffi_syntax}.

Fixpoint decode (r : field_repr) (v : val) : option (carrier r) :=
  match r return option (carrier r) with
  | Unit => match v with LitV LitUnit => Some tt | _ => None end
  | Bool => match v with LitV (LitBool b) => Some b | _ => None end
  | Uint8 => match v with LitV (LitByte w) => Some w | _ => None end
  | Uint64 | Int64 => match v with LitV (LitInt w) => Some w | _ => None end
  | Pointer => match v with LitV (LitLoc l) => Some l | _ => None end
  | String => match v with LitV (LitString s) => Some s | _ => None end
  | Array n element =>
      match v with
      | ArrayV vs => if Nat.eqb (List.length vs) n then traverse (decode element) vs else None
      | _ => None
      end
  end.

Lemma reject_empty_four : decode (Array 4 Uint64) (ArrayV []) = None.
Proof. reflexivity. Qed.

Lemma decode_encode r : forall x, wellformed r x -> decode r (encode r x) = Some x.
Proof.
  induction r; intros x H; cbn; try reflexivity.
  - now destruct x.
  - destruct H as [Hlen Hxs]. rewrite List.length_map Hlen Nat.eqb_refl.
    eapply traverse_map; eauto.
Qed.

Lemma decode_sound r : forall v x, decode r v = Some x -> encode r x = v /\ wellformed r x.
Proof.
  induction r; intros v x H; destruct v; cbn in H; try discriminate;
    try match goal with lit : base_lit |- _ =>
      destruct lit; try discriminate; inversion H; subst; split; reflexivity
    end.
  destruct (Nat.eqb (List.length vs) length) eqn:Hlen; try discriminate.
  apply Nat.eqb_eq in Hlen.
  destruct (traverse_sound (encode r) (decode r) (wellformed r) IHr _ _ H) as [He Hwf].
  split; [cbn; now rewrite He|]. split; [|exact Hwf].
  rewrite <- Hlen. rewrite <- He. rewrite List.length_map. reflexivity.
Qed.

Lemma wrong_array_length n element vs : List.length vs ≠ n ->
  decode (Array n element) (ArrayV vs) = None.
Proof.
  intros Hlen. cbn. destruct (Nat.eqb (List.length vs) n) eqn:H; [|reflexivity].
  apply Nat.eqb_eq in H. contradiction.
Qed.

End decoding.

Fixpoint replace_at {A : Type} (i : nat) (y : A) (xs : list A) : list A :=
  match xs, i with
  | [], _ => []
  | _ :: tail, O => y :: tail
  | head :: tail, S j => head :: replace_at j y tail
  end.

Lemma replace_length {A : Type} i (y : A) xs : List.length (replace_at i y xs) = List.length xs.
Proof. revert i. induction xs; intros [|i]; cbn; auto. Qed.

Lemma replace_forall {A : Type} (P : A -> Prop) i y xs :
  P y -> Forall P xs -> Forall P (replace_at i y xs).
Proof.
  intros Hy Hxs. revert i. induction Hxs; intros [|i]; cbn; constructor; auto.
Qed.

Lemma replace_here {A : Type} i (y : A) xs : (i < List.length xs)%nat ->
  List.nth_error (replace_at i y xs) i = Some y.
Proof.
  revert i. induction xs; intros [|i] H; cbn in *; try lia; auto.
  apply IHxs. lia.
Qed.

Lemma replace_elsewhere {A : Type} i j (y : A) xs : i ≠ j ->
  List.nth_error (replace_at i y xs) j = List.nth_error xs j.
Proof.
  revert i j. induction xs; intros [|i] [|j] H; cbn; try reflexivity; try congruence.
  apply IHxs. congruence.
Qed.

Section array_access.
Context {ext : ffi_syntax}.

Lemma encoded_lookup element xs i :
  List.nth_error (List.map (encode element) xs) i =
  option_map (encode element) (List.nth_error xs i).
Proof. apply List.nth_error_map. Qed.

Lemma bounded_lookup n element xs i : wellformed (Array n element) xs -> (i < n)%nat ->
  exists x, List.nth_error xs i = Some x /\ wellformed element x /\
    List.nth_error (List.map (encode element) xs) i = Some (encode element x).
Proof.
  intros [Hlen Hwf] Hi.
  destruct (List.nth_error xs i) as [x|] eqn:Hx.
  - exists x. split; first reflexivity. split.
    + rewrite List.Forall_forall in Hwf. apply Hwf. eapply List.nth_error_In. exact Hx.
    + rewrite encoded_lookup Hx. reflexivity.
  - apply List.nth_error_None in Hx. lia.
Qed.

Lemma replace_wellformed n element xs i y :
  wellformed (Array n element) xs -> wellformed element y ->
  wellformed (Array n element) (replace_at i y xs).
Proof.
  intros [Hlen Hwf] Hy. split; first now rewrite replace_length.
  apply replace_forall; assumption.
Qed.

End array_access.

(* Calls also carry function values and nested argument/result tuples. *)
Inductive call_repr := Atom (r : field_repr) | Function | Tuple (left right : call_repr).

Section calls.
Context {ext : ffi_syntax}.
Fixpoint call_carrier r : Type :=
  match r with
  | Atom a => carrier a
  | Function => func.t
  | Tuple a b => (call_carrier a * call_carrier b)%type
  end.
Fixpoint call_wellformed r : call_carrier r -> Prop :=
  match r return call_carrier r -> Prop with
  | Atom a => wellformed a
  | Function => fun _ => True
  | Tuple a b => fun x => call_wellformed a (fst x) /\ call_wellformed b (snd x)
  end.
Fixpoint call_encode r : call_carrier r -> val :=
  match r return call_carrier r -> val with
  | Atom a => encode a
  | Function => fun f => RecV f.(func.f) f.(func.x) f.(func.e)
  | Tuple a b => fun x => PairV (call_encode a (fst x)) (call_encode b (snd x))
  end.
Fixpoint call_decode r (v : val) : option (call_carrier r) :=
  match r return option (call_carrier r) with
  | Atom a => decode a v
  | Function => match v with RecV f x e => Some (func.mk f x e) | _ => None end
  | Tuple a b => match v with
      | PairV x y => match call_decode a x, call_decode b y with
          | Some x', Some y' => Some (x', y') | _, _ => None end
      | _ => None end
  end.

Lemma call_roundtrip r : forall x, call_wellformed r x -> call_decode r (call_encode r x) = Some x.
Proof.
  induction r; intros x H; cbn in *.
  - now apply decode_encode.
  - now destruct x.
  - destruct x as [x y], H as [Hx Hy]. cbn in *.
    now rewrite (IHr1 x Hx) (IHr2 y Hy).
Qed.

Lemma call_sound r : forall v x, call_decode r v = Some x -> call_encode r x = v /\ call_wellformed r x.
Proof.
  induction r; intros v x H; cbn in *.
  - now apply decode_sound.
  - destruct v; try discriminate. inversion H; subst. split; reflexivity.
  - destruct v; try discriminate.
    destruct (call_decode r1 v1) as [a|] eqn:Ha; try discriminate.
    destruct (call_decode r2 v2) as [b|] eqn:Hb; try discriminate.
    inversion H; subst x. destruct (IHr1 _ _ Ha) as [Hea Hwa].
    destruct (IHr2 _ _ Hb) as [Heb Hwb]. cbn. rewrite Hea Heb.
    split; [reflexivity|now split].
Qed.

Lemma call_injective r x y :
  call_wellformed r x -> call_wellformed r y -> call_encode r x = call_encode r y -> x = y.
Proof.
  intros Hx Hy He. apply (f_equal (call_decode r)) in He.
  rewrite (call_roundtrip r x Hx) (call_roundtrip r y Hy) in He. now inversion He.
Qed.
End calls.
