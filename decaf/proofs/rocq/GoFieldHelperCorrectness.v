From New.golang Require Import defn.
From Stdlib Require Import ZArith Lia.
Require Import GoFieldEncoding GoFieldSyntax GoFieldEval GoFieldHelperExecution
  GoCarryArithmetic GoBorrowArithmetic GoMultiplyArithmetic.
Open Scope Z_scope.

Lemma executed_add_correct x y carry : word.unsigned carry <= 1 ->
  exists lo hi : w64,
    option_map fst (evaluate 160 (add_call x y carry) []) =
      Some (PairV (encode Uint64 lo) (encode Uint64 hi)) /\
    word.unsigned lo + 2^64 * word.unsigned hi =
      word.unsigned x + word.unsigned y + word.unsigned carry /\
    0 <= word.unsigned lo < 2^64 /\ 0 <= word.unsigned hi <= 1.
Proof.
  intros Hc.
  exists (word.add (word.add x y) carry),
    (word.sru (word.or (word.and x y)
      (word.and (word.or x y) (word.not (word.add (word.add x y) carry)))) (W64 63)).
  split; [exact (actual_add_executes x y carry)|].
  pose proof (addcarry_words x y carry Hc) as [L H]. rewrite L H.
  pose proof (word.unsigned_range x). pose proof (word.unsigned_range y).
  pose proof (word.unsigned_range carry).
  pose proof (Z.div_mod (word.unsigned x + word.unsigned y + word.unsigned carry) (2^64) ltac:(lia)).
  pose proof (Z.mod_pos_bound (word.unsigned x + word.unsigned y + word.unsigned carry) (2^64) ltac:(lia)).
  assert (0 <= (word.unsigned x + word.unsigned y + word.unsigned carry) / 2^64 < 2).
  { split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]. }
  lia.
Qed.

Lemma executed_sub_correct x y borrow : word.unsigned borrow <= 1 ->
  exists lo hi : w64,
    option_map fst (evaluate 160 (sub_call x y borrow) []) =
      Some (PairV (encode Uint64 lo) (encode Uint64 hi)) /\
    word.unsigned lo - 2^64 * word.unsigned hi =
      word.unsigned x - word.unsigned y - word.unsigned borrow /\
    0 <= word.unsigned lo < 2^64 /\ 0 <= word.unsigned hi <= 1.
Proof.
  intros Hc.
  exists (word.sub (word.sub x y) borrow),
    (word.sru (word.or (word.and (word.not x) y)
      (word.and (word.not (word.xor x y)) (word.sub (word.sub x y) borrow))) (W64 63)).
  split; [exact (actual_sub_executes x y borrow)|].
  pose proof (subborrow_words x y borrow Hc) as [L H]. rewrite L H.
  pose proof (word.unsigned_range x). pose proof (word.unsigned_range y).
  pose proof (word.unsigned_range borrow).
  pose proof (Z.div_mod (word.unsigned x - word.unsigned y - word.unsigned borrow) (2^64) ltac:(lia)).
  pose proof (Z.mod_pos_bound (word.unsigned x - word.unsigned y - word.unsigned borrow) (2^64) ltac:(lia)).
  assert (-1 <= (word.unsigned x - word.unsigned y - word.unsigned borrow) / 2^64 < 1).
  { split; [apply Z.div_le_lower_bound; lia|apply Z.div_lt_upper_bound; lia]. }
  lia.
Qed.

Lemma executed_mul_correct x y :
  exists hi lo : w64,
    option_map fst (evaluate 240 (mul_call x y) []) =
      Some (PairV (encode Uint64 hi) (encode Uint64 lo)) /\
    word.unsigned lo + 2^64 * word.unsigned hi = word.unsigned x * word.unsigned y /\
    0 <= word.unsigned lo < 2^64 /\ 0 <= word.unsigned hi < 2^64.
Proof.
  exists (fst (product_words x y)), (snd (product_words x y)).
  split; [exact (actual_mul_executes x y)|].
  pose proof (multiply_words x y) as H.
  destruct (product_words x y) as [hi lo]. cbn in *.
  destruct H as [L H].
  pose proof (word.unsigned_range hi). pose proof (word.unsigned_range lo).
  split; [|lia]. rewrite L H.
  pose proof (Z.div_mod (word.unsigned x * word.unsigned y) (2^64) ltac:(lia)). lia.
Qed.

(* Correctness under the explicit field evaluator, not yet native Go refinement. *)
