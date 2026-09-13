From Stdlib Require Import ZArith Lia.
From Core Require Import Core.
From Slice Require Import Decaf_proof_slice_Fiat.
Open Scope Z_scope.

(* A concrete source-mutation control, not a replacement for multiply_exact. *)
Theorem multiply_zero_witness :
  U32.raw (fst (fq_mulx_u32 (0 : t_u32) (0 : t_u32)
                            (0 : t_u32) (0 : t_u32))) = 0.
Proof. cbn. lia. Qed.
