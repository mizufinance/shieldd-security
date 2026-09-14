From New.golang Require Import defn.
Require Import GoFieldEncoding GoFieldSyntax GoFieldHeap GoFieldEval GoFullSpecialization.

Definition add_call (x y carry : w64) : @expr field_syntax :=
  App (App (App (Val literal_bits.Add64ⁱᵐᵖˡ) (Val (encode Uint64 x)))
    (Val (encode Uint64 y))) (Val (encode Uint64 carry)).

Definition add_result (x y carry : w64) : @val field_syntax :=
  let sum := word.add (word.add x y) carry in
  let carry_out := word.sru (word.or (word.and x y)
    (word.and (word.or x y) (word.not sum))) (W64 63) in
  PairV (encode Uint64 sum) (encode Uint64 carry_out).

Lemma actual_add_executes x y carry :
  option_map fst (evaluate 160 (add_call x y carry) []) = Some (add_result x y carry).
Proof. reflexivity. Qed.

Definition sub_call (x y borrow : w64) : @expr field_syntax :=
  App (App (App (Val literal_bits.Sub64ⁱᵐᵖˡ) (Val (encode Uint64 x)))
    (Val (encode Uint64 y))) (Val (encode Uint64 borrow)).
Definition sub_result (x y borrow : w64) : @val field_syntax :=
  let diff := word.sub (word.sub x y) borrow in
  let borrow_out := word.sru (word.or (word.and (word.not x) y)
    (word.and (word.not (word.xor x y)) diff)) (W64 63) in
  PairV (encode Uint64 diff) (encode Uint64 borrow_out).
Lemma actual_sub_executes x y borrow :
  option_map fst (evaluate 160 (sub_call x y borrow) []) = Some (sub_result x y borrow).
Proof. reflexivity. Qed.

Definition mul_call (x y : w64) : @expr field_syntax :=
  App (App (Val literal_bits.Mul64ⁱᵐᵖˡ) (Val (encode Uint64 x))) (Val (encode Uint64 y)).
Definition mul_result (x y : w64) : @val field_syntax :=
  let mask := W64 4294967295 in
  let x0 := word.and x mask in let x1 := word.sru x (W64 32) in
  let y0 := word.and y mask in let y1 := word.sru y (W64 32) in
  let w0 := word.mul x0 y0 in
  let t := word.add (word.mul x1 y0) (word.sru w0 (W64 32)) in
  let w1 := word.and t mask in let w2 := word.sru t (W64 32) in
  let w1 := word.add w1 (word.mul x0 y1) in
  let hi := word.add (word.add (word.mul x1 y1) w2) (word.sru w1 (W64 32)) in
  PairV (encode Uint64 hi) (encode Uint64 (word.mul x y)).
Lemma actual_mul_executes x y :
  option_map fst (evaluate 240 (mul_call x y) []) = Some (mul_result x y).
Proof. reflexivity. Qed.

Definition cmov_call (selector x y : w64) : @expr field_syntax :=
  App (App (App (App (Val literal_fiat.FqCmovznzU64ⁱᵐᵖˡ)
    (Val (encode Pointer (Loc 1 0)))) (Val (encode Uint64 selector)))
    (Val (encode Uint64 x))) (Val (encode Uint64 y)).
Definition cmov_result (selector x y : w64) :=
  let mask := word.mul selector (W64 18446744073709551615) in
  word.or (word.and mask y) (word.and (word.not mask) x).
Lemma actual_cmov_writes selector x y old :
  match evaluate 160 (cmov_call selector x y) [[encode Uint64 old]] with
  | Some (_, h) => read_address h (Loc 1 0) | None => None end =
  Some (encode Uint64 (cmov_result selector x y)).
Proof. reflexivity. Qed.

Lemma pair_allocation_order x y :
  evaluate 8
    (Pair (App (Val (GoInstruction (GoAlloc go.uint64))) (Val (encode Uint64 x)))
          (App (Val (GoInstruction (GoAlloc go.uint64))) (Val (encode Uint64 y)))) [] =
  Some (PairV (encode Pointer (Loc 1 0)) (encode Pointer (Loc 2 0)),
        [[encode Uint64 x]; [encode Uint64 y]]).
Proof. reflexivity. Qed.

(* Actual specialized helper bodies under the field-slice evaluator. Arithmetic
   interpretation, native correspondence, and the full execution relation are
   additional obligations; arbitrary carry words here specify the body exactly. *)
