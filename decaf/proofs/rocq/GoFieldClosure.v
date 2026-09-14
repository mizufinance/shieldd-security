From Perennial.goose_lang Require Import lang.

Section closure.
Context {ext : ffi_syntax}.
Variable known_function : go_string -> bool.

Definition field_instruction (i : go_instruction) : bool :=
  match i with
  | Convert _ _ | GoUnOp _ _ | GoLoad _ | GoStore _ | GoAlloc _ | GoZeroVal _
  | IndexRef _ | Index _ | ArraySet | ArrayLength => true
  | GoOp GoDiv _ | GoOp GoRemainder _ => false
  | GoOp _ _ => true
  | FuncResolve name [] => known_function name
  | _ => false
  end.

(* Reject unsupported syntax rather than omitting its children. This is a
   syntax-closure check, not a proof of instruction correctness or termination. *)
Fixpoint field_expr (e : expr) : bool :=
  match e with
  | Val v => field_value v
  | Var _ => true
  | Rec BAnon _ body => field_expr body
  | App f x | Pair f x => field_expr f && field_expr x
  | If c yes no => field_expr c && field_expr yes && field_expr no
  | Fst x | Snd x => field_expr x
  | _ => false
  end
with field_value (v : val) : bool :=
  match v with
  | LitV (LitInt _) | LitV (LitByte _) | LitV (LitBool _) | LitV (LitString _)
  | LitV LitUnit | LitV (LitLoc _) => true
  | RecV BAnon _ body => field_expr body
  | PairV x y => field_value x && field_value y
  | InjLV v => field_value v
  | GoInstruction i => field_instruction i
  | _ => false
  end.

Lemma foreign_calls_rejected op e : field_expr (ExternalOp op e) = false.
Proof. reflexivity. Qed.
Lemma fork_rejected e : field_expr (Fork e) = false.
Proof. reflexivity. Qed.
Lemma unknown_resolver_rejected name : known_function name = false ->
  field_value (GoInstruction (FuncResolve name [])) = false.
Proof. exact (fun H => H). Qed.
End closure.
