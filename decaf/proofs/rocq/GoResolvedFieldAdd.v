(* The helper and named-type contracts are constructed, not assumed here.
   PreSemantics is still required for the modified dispatch instance. A base
   instance alone would not prove compatibility or model inhabitance. *)
From New.code.mizufinance_local.decaf Require Import fiat.
From New.golang.theory Require Import auto array.
Require Import GoFieldResolver GoFieldAdd GoFrFieldAdd.

Section resolved.
Context `{ffi_sem : ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  (base : GoSemanticsFunctions).
Local Instance selected : GoSemanticsFunctions := field_semantics base.
Context {pre_sem : @go.PreSemantics _ _ _ selected}.

Local Instance fq_named : fiat.FqUint1_Assumptions := contract_FqUint1 base.
Local Instance fr_named : fiat.FrUint1_Assumptions := contract_FrUint1 base.
Local Instance add64_body : FuncUnfold bits.Add64 [] bits.Add64ⁱᵐᵖˡ := unfold_Add64 base.
Local Instance sub64_body : FuncUnfold bits.Sub64 [] bits.Sub64ⁱᵐᵖˡ := unfold_Sub64 base.
Local Instance fq_select_body : FuncUnfold fiat.FqCmovznzU64 [] fiat.FqCmovznzU64ⁱᵐᵖˡ := unfold_FqCmovznzU64 base.
Local Instance fr_select_body : FuncUnfold fiat.FrCmovznzU64 [] fiat.FrCmovznzU64ⁱᵐᵖˡ := unfold_FrCmovznzU64 base.

Definition resolved_fq_add := GoFieldAdd.add_correct.
Definition resolved_fr_add := GoFrFieldAdd.add_correct.
End resolved.
