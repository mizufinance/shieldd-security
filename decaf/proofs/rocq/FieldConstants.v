(* Shared mathematical foundations; no native execution or encoding claim. *)
From Stdlib Require Import ZArith Znumtheory List Lia.
From Coqprime.PrimalityTest Require Import PocklingtonCertificat.
Import ListNotations.

Definition fq_modulus : Z :=
  8444461749428370424248824938781546531375899335154063827935233455917409239041.
Definition fr_modulus : Z :=
  2111115437357092606062206234695386632838870926408408195193685246394721360383.

Local Open Scope positive_scope.

Theorem fq_prime_legacy : prime fq_modulus.
Proof.
  unfold fq_modulus.
  apply (Pocklington_refl
    (Pock_certif
      8444461749428370424248824938781546531375899335154063827935233455917409239041
      11 [(2,47); (9586122913090633729,2)] 1)
    [Pock_certif 9586122913090633729 11 [(2,46)] 1;
     Proof_certif 2 prime_2]).
  vm_compute. reflexivity.
Qed.

Theorem fr_prime_legacy : prime fr_modulus.
Proof.
  unfold fr_modulus.
  apply (Pocklington_refl
    (Pock_certif
      2111115437357092606062206234695386632838870926408408195193685246394721360383
      5 [(2,1); (1553,1); (1282495723,1); (4153589585267,1)]
      26470200319961613971875942)
    [Pock_certif 4153589585267 2 [(2,1); (11,1); (188799526603,1)] 1;
     Pock_certif 188799526603 3 [(2,1); (3,2); (17,1); (71,1); (1187,1); (7321,1)] 1;
     Pock_certif 1282495723 5 [(2,1); (3,1); (229,1); (933403,1)] 1;
     Pock_certif 933403 2 [(2,1); (3,1); (17,1); (9151,1)] 1;
     Pock_certif 9151 3 [(2,1); (3,1); (5,2); (61,1)] 1;
     Pock_certif 7321 7 [(2,3); (3,1); (5,1); (61,1)] 1;
     Pock_certif 1553 3 [(2,4); (97,1)] 1;
     Pock_certif 1187 2 [(2,1); (593,1)] 1;
     Pock_certif 593 3 [(2,4); (37,1)] 1;
     Pock_certif 229 6 [(2,2); (3,1); (19,1)] 1;
     Pock_certif 97 5 [(2,5); (3,1)] 1;
     Pock_certif 71 7 [(2,1); (5,1); (7,1)] 1;
     Pock_certif 61 2 [(2,2); (3,1); (5,1)] 1;
     Pock_certif 37 2 [(2,2); (3,2)] 1;
     Pock_certif 19 2 [(2,1); (3,2)] 1;
     Pock_certif 17 3 [(2,4)] 1;
     Pock_certif 11 2 [(2,1); (5,1)] 1;
     Pock_certif 7 3 [(2,1); (3,1)] 1;
     Pock_certif 5 2 [(2,2)] 1;
     Pock_certif 3 2 [(2,1)] 1;
     Proof_certif 2 prime_2]).
  vm_compute. reflexivity.
Qed.

Theorem fq_prime : Z.prime fq_modulus.
Proof. apply prime_alt. exact fq_prime_legacy. Qed.

Theorem fr_prime : Z.prime fr_modulus.
Proof. apply prime_alt. exact fr_prime_legacy. Qed.

Theorem fq_representation_bound : (0 < fq_modulus < 2^253)%Z.
Proof. unfold fq_modulus; vm_compute; intuition discriminate. Qed.

Theorem fr_representation_bound : (0 < fr_modulus < 2^251)%Z.
Proof. unfold fr_modulus; vm_compute; intuition discriminate. Qed.
