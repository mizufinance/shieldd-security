From New.golang.defn Require Import exception.
Require Import GoFieldEncoding.

Section explicit_control.
Context {ext : ffi_syntax}.

Definition literal_execute : val := PairV (encode String "execute"%go) (encode Unit tt).
Definition literal_return (v : val) : val := PairV (encode String "return"%go) v.
Definition literal_do_execute : val := λ: "_v", (encode String "execute"%go, encode Unit tt).
Definition literal_do_return : val := λ: "v", (encode String "return"%go, Var "v").
Definition literal_seq : val :=
  λ: "s2" "s1",
    if: (Fst "s1") =⟨go.string⟩ (encode String "execute"%go) then
      "s2" (encode Unit tt)
    else "s1".
Definition literal_do : val := λ: "v", Snd "v".

(* A checked correspondence for the old combinators, not an inhabitance claim. *)
Section compatibility.
Context {go_gctx : GoGlobalContext}.
Hypothesis unit_encoding : (into_val tt : val) = encode Unit tt.
Hypothesis string_encoding : forall s : go_string, (into_val s : val) = encode String s.

Lemma execute_agrees : execute_val = literal_execute.
Proof. rewrite execute_val_unseal /execute_val_def unit_encoding string_encoding. reflexivity. Qed.
Lemma return_agrees v : return_val v = literal_return v.
Proof. rewrite return_val_unseal /return_val_def string_encoding. reflexivity. Qed.
Lemma do_execute_agrees : do_execute = literal_do_execute.
Proof. rewrite do_execute_unseal /exception.do_execute_def unit_encoding string_encoding. reflexivity. Qed.
Lemma do_return_agrees : do_return = literal_do_return.
Proof. rewrite do_return_unseal /exception.do_return_def string_encoding. reflexivity. Qed.
Lemma seq_agrees : exception_seq = literal_seq.
Proof. rewrite exception_seq_unseal /exception.exception_seq_def unit_encoding string_encoding. reflexivity. Qed.
Lemma do_agrees : exception_do = literal_do.
Proof. rewrite exception_do_unseal. reflexivity. Qed.
End compatibility.
End explicit_control.
