From Perennial.goose_lang Require Import lang.

(* The generated field slice has no external opcodes or external values. *)
Definition field_syntax : ffi_syntax :=
  {| ffi_opcode := Empty_set; ffi_val := Empty_set |}.

Definition field_state_model : ffi_model :=
  {| ffi_state := unit; ffi_global_state := unit |}.

Lemma no_external_opcode (op : @ffi_opcode field_syntax) : False.
Proof. destruct op. Qed.
Lemma no_external_value (v : @ffi_val field_syntax) : False.
Proof. destruct v. Qed.

