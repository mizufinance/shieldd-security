From New.golang Require Import defn.
Require Import GoFieldTypes GoFieldSyntax GoFullSpecialization.

Definition scalar_known t := match scalar_type t with Some _ => true | None => false end.
Definition array_known t := match t with
  | go.ArrayType n elem => bool_decide (n = 4 \/ n = 5) && bool_decide (elem = go.uint64) ||
                          bool_decide (n = 32) && bool_decide (elem = go.uint8)
  | _ => false end.

Definition instruction_shape i : bool :=
  match i with
  | GoOp op t => match scalar_type t, op with
    | Some U64, GoDiv | Some U64, GoRemainder | Some I64, GoDiv | Some I64, GoRemainder => false
    | Some U64, _ | Some I64, _ => true
    | Some U8, GoAnd | Some Boolean, GoEquals | Some Bytes, GoEquals => true
    | _, _ => false end
  | GoUnOp op t => match scalar_type t, op with
    | Some U64, GoPos | Some U64, GoNeg | Some U64, GoComplement
    | Some I64, GoPos | Some I64, GoNeg | Some I64, GoComplement
    | Some Integer, GoPos | Some Integer, GoNeg | Some Boolean, GoNot => true
    | _, _ => false end
  | Convert source target => match scalar_type source, scalar_type target with
    | Some PointerKind, Some PointerKind => bool_decide (source = target)
    | Some U64, Some U64 | Some U64, Some I64 | Some U64, Some U8
    | Some I64, Some U64 | Some I64, Some I64 | Some I64, Some U8
    | Some U8, Some U64 | Some U8, Some I64 | Some U8, Some U8
    | Some Integer, Some U64 | Some Integer, Some I64 | Some Integer, Some U8 => true
    | _, _ => false end
  | GoLoad t | GoStore t | GoAlloc t | GoZeroVal t => scalar_known t || array_known t
  | IndexRef t | Index t => array_known t
  | ArraySet | ArrayLength | FuncResolve _ [] => true
  | _ => false end.

(* This checks instruction/type shapes only. It does not establish operand
   typing, constant representability, valid shift counts, memory access, named
   call bindings, or execution. The existing dispatcher supplies call bindings. *)
Fixpoint shaped_expr (e : @expr field_syntax) : bool :=
  match e with
  | Val v => shaped_value v
  | Var _ => true
  | Rec BAnon _ body => shaped_expr body
  | App f x | Pair f x => shaped_expr f && shaped_expr x
  | If c yes no => shaped_expr c && shaped_expr yes && shaped_expr no
  | Fst x | Snd x => shaped_expr x
  | _ => false end
with shaped_value (v : @val field_syntax) : bool :=
  match v with
  | LitV _ => true
  | RecV BAnon _ body => shaped_expr body
  | PairV x y => shaped_value x && shaped_value y
  | InjLV v => shaped_value v
  | GoInstruction i => instruction_shape i
  | _ => false end.
