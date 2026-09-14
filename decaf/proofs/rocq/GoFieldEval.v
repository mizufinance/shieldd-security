From New.golang Require Import defn.
Require Import GoFieldEncoding GoFieldSyntax GoFieldTypes GoFieldPure GoFieldReference GoFieldHeap GoLiteralDispatch.

Definition instruction (op : go_instruction) (arg : @val field_syntax) (h : field_heap)
  : option ((@val field_syntax) * field_heap) :=
  match op with
  | GoAlloc t => match scalar_type t with
    | Some k => if scalar_matches k arg then
      let '(l, h') := allocate_cell h arg in Some (encode Pointer l, h') else None
    | None => None end
  | GoLoad t => match scalar_type t, decode Pointer arg with
    | Some k, Some l => match read_address h l with
      | Some v => if scalar_matches k v then Some (v, h) else None
      | None => None end
    | _, _ => None end
  | GoStore t => match scalar_type t, arg with
    | Some k, PairV pointer value => match decode Pointer pointer with
      | Some l => if scalar_matches k value then
        match read_address h l with
        | Some old => if scalar_matches k old then
          option_map (fun h' => (encode Unit tt, h')) (write_address h l value) else None
        | None => None end
        else None
      | None => None end
    | _, _ => None end
  | IndexRef (go.ArrayType n elem) =>
    if decide (elem = go.uint64 \/ elem = go.uint8) then
      match decode_reference n arg with
      | Some (Reference l) => Some (encode Pointer l, h)
      | _ => None end
    else None
  | FuncResolve name [] => option_map (fun v => (v, h)) (dispatch name)
  | _ => option_map (fun v => (v, h)) (pure_instruction op arg)
  end.

Fixpoint evaluate (fuel : nat) (e : @expr field_syntax) (h : field_heap)
  : option ((@val field_syntax) * field_heap) :=
  match fuel with
  | O => None
  | S fuel =>
    match e with
    | Val v => Some (v, h)
    | Rec BAnon binder body => Some (RecV BAnon binder body, h)
    | App f x =>
      match evaluate fuel x h with
      | Some (arg, h1) => match evaluate fuel f h1 with
        | Some (RecV BAnon binder body, h2) => evaluate fuel (subst' binder arg body) h2
        | Some (GoInstruction op, h2) => instruction op arg h2
        | _ => None end
      | None => None end
    | Pair x y =>
      match evaluate fuel x h with
      | Some (x, h1) => match evaluate fuel y h1 with
        | Some (y, h2) => Some (PairV x y, h2) | None => None end
      | None => None end
    | Fst e => match evaluate fuel e h with
      | Some (PairV x _, h') => Some (x, h') | _ => None end
    | Snd e => match evaluate fuel e h with
      | Some (PairV _ y, h') => Some (y, h') | _ => None end
    | If cond yes no => match evaluate fuel cond h with
      | Some (LitV (LitBool b), h') => evaluate fuel (if b then yes else no) h'
      | _ => None end
    | _ => None end
  end.

Lemma evaluation_deterministic fuel e h x y :
  evaluate fuel e h = Some x -> evaluate fuel e h = Some y -> x = y.
Proof. congruence. Qed.

(* Executable field-slice prototype. Fuel exhaustion and unsupported/error
   states all return None; successful native progress, resource bounds, Go
   panic behavior, concurrency, and semantic correspondence are not proved. *)
