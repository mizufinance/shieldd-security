(* Typed Fiat arithmetic pipeline only. Native execution and printer correspondence
   are separate obligations. Go's cmovznz-by-mul option selects emitted helpers;
   it is not a PipelineOptions field and is not proved by this module. *)
From Stdlib Require Import ZArith List String Derive.
Require Import Crypto.PushButtonSynthesis.Primitives.
Require Import Crypto.PushButtonSynthesis.WordByWordMontgomery.
Require Import Crypto.Language.API.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Stringification.Language.
Import Compilers.Options.
Import ListNotations.
Open Scope Z_scope.

Local Existing Instance default_PipelineOptions | 100.
Definition rust32_options : PipelineOptions :=
  {| output_options :=
       {| skip_typedefs_ := true;
          relax_adc_sbb_return_carry_to_bitwidth_ := [];
          language_specific_cast_adjustment_ := true |};
     widen_carry := false; widen_bytes := false;
     should_split_mul := false; should_split_multiret := false;
     no_select := false; only_signed := false |}.
Definition go64_options : PipelineOptions :=
  {| output_options :=
       {| skip_typedefs_ := true;
          relax_adc_sbb_return_carry_to_bitwidth_ := [32;64];
          language_specific_cast_adjustment_ := true |};
     widen_carry := false; widen_bytes := false;
     should_split_mul := true; should_split_multiret := false;
     no_select := false; only_signed := false |}.

Definition fq : Z := 8444461749428370424248824938781546531375899335154063827935233455917409239041.
Definition fr : Z := 2111115437357092606062206234695386632838870926408408195193685246394721360383.

Module RustFq.
Local Instance pipeline : PipelineOptions := rust32_options.
Derive body SuchThat (WordByWordMontgomery.mul fq 32 = Success body) As pipeline_success.
Proof. vm_compute. reflexivity. Qed.
Lemma arguments : WordByWordMontgomery.check_args fq 32 [] (Success tt) = Success tt.
Proof. vm_compute. reflexivity. Qed.
Definition correct := @WordByWordMontgomery.mul_correct pipeline fq 32 [] arguments body pipeline_success.
Print Assumptions correct.
End RustFq.

Module GoFq.
Local Instance pipeline : PipelineOptions := go64_options.
Derive body SuchThat (WordByWordMontgomery.mul fq 64 = Success body) As pipeline_success.
Proof. vm_compute. reflexivity. Qed.
Lemma arguments : WordByWordMontgomery.check_args fq 64 [] (Success tt) = Success tt.
Proof. vm_compute. reflexivity. Qed.
Definition correct := @WordByWordMontgomery.mul_correct pipeline fq 64 [] arguments body pipeline_success.
Print Assumptions correct.
End GoFq.

Module RustFr.
Local Instance pipeline : PipelineOptions := rust32_options.
Derive body SuchThat (WordByWordMontgomery.mul fr 32 = Success body) As pipeline_success.
Proof. vm_compute. reflexivity. Qed.
Lemma arguments : WordByWordMontgomery.check_args fr 32 [] (Success tt) = Success tt.
Proof. vm_compute. reflexivity. Qed.
Definition correct := @WordByWordMontgomery.mul_correct pipeline fr 32 [] arguments body pipeline_success.
Print Assumptions correct.
End RustFr.

Module GoFr.
Local Instance pipeline : PipelineOptions := go64_options.
Derive body SuchThat (WordByWordMontgomery.mul fr 64 = Success body) As pipeline_success.
Proof. vm_compute. reflexivity. Qed.
Lemma arguments : WordByWordMontgomery.check_args fr 64 [] (Success tt) = Success tt.
Proof. vm_compute. reflexivity. Qed.
Definition correct := @WordByWordMontgomery.mul_correct pipeline fr 64 [] arguments body pipeline_success.
Print Assumptions correct.
End GoFr.
