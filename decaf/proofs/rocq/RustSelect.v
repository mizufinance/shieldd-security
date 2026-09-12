From Stdlib Require Import ZArith Lia.
From Core Require Import Core.
From Slice Require Import Decaf_proof_slice_Fiat.
Open Scope Z_scope.

Theorem select_exact out carry x y :
  0 <= U8.raw carry <= 1 -> U32.canonical x -> U32.canonical y ->
  fq_cmovznz_u32 out carry x y = if U8.raw carry =? 0 then x else y.
Proof.
  destruct carry as [c], x as [x], y as [y].
  unfold U8.raw, U32.canonical, U32.raw, F32.width.
  cbn [U32.raw]. intros Hc Hx Hy.
  assert (Hbit : c = 0 \/ c = 1) by lia. destruct Hbit; subst c.
  - change (U32.Word (((Z.land 4294967295 x) mod 2^32) mod 2^32) = U32.Word x).
    rewrite Z.land_comm. change 4294967295 with (Z.ones 32).
    rewrite Z.land_ones by lia. rewrite !Z.mod_mod by lia.
    rewrite Z.mod_small by lia. reflexivity.
  - change (U32.Word ((Z.lor ((Z.land 4294967295 y) mod 2^32) 0) mod 2^32) = U32.Word y).
    rewrite Z.lor_0_r, Z.land_comm. change 4294967295 with (Z.ones 32).
    rewrite Z.land_ones by lia. rewrite !Z.mod_mod by lia.
    rewrite Z.mod_small by lia. reflexivity.
Qed.

Theorem select_safety carry :
  0 <= U8.raw carry <= 1 -> -2^7 <= 0-U8.raw carry < 2^7.
Proof. lia. Qed.
