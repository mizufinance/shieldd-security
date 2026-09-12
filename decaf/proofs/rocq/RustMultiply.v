From Stdlib Require Import ZArith Lia.
From Core Require Import Core.
From Slice Require Import Decaf_proof_slice_Fiat.
Open Scope Z_scope.

Theorem multiply_exact out1 out2 x y :
  U32.canonical x -> U32.canonical y ->
  fq_mulx_u32 out1 out2 x y =
    (U32.of_Z (U32.raw x * U32.raw y),
     U32.of_Z ((U32.raw x * U32.raw y) / 2^32)).
Proof.
  destruct x as [x], y as [y].
  unfold U32.canonical, U32.raw, F32.width. intros Hx Hy.
  assert (Hp : 0 <= x*y < 2^64) by nia.
  unfold fq_mulx_u32, cast, f_mul, f_bitand, f_shr.
  cbn [integer_u32 integer_u64 integer_i32 value from_Z
       U32.value U64.value I32.value U32.raw U64.raw I32.raw
       U32.of_Z U64.of_Z I32.of_Z F32.width F64.width S32.width
       F32.signed F64.signed S32.signed].
  unfold U32.value, U64.value, I32.value, U32.of_Z, U64.of_Z, I32.of_Z,
    U32.raw, U64.raw, I32.raw in *.
  cbn -[Z.shiftr] in *.
  rewrite (Z.mod_small x 18446744073709551616) by lia.
  rewrite (Z.mod_small y 18446744073709551616) by lia.
  rewrite (Z.mod_small (x*y) 18446744073709551616) by lia.
  change 4294967295 with (Z.ones 32).
  rewrite Z.land_ones by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2^32) with 4294967296.
  assert (Hr : 0 <= (x*y) mod 4294967296 < 4294967296)
    by (apply Z.mod_pos_bound; lia).
  assert (Hq : 0 <= (x*y) / 4294967296 < 4294967296).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite (Z.mod_small ((x*y) mod 4294967296) 18446744073709551616) by lia.
  rewrite (Z.mod_small ((x*y) / 4294967296) 18446744073709551616) by lia.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Theorem multiply_safety x y :
  U32.canonical x -> U32.canonical y ->
  0 <= U32.raw x * U32.raw y < 2^64 /\
  @shift_defined t_u64 t_i32 integer_u64 integer_i32 (32 : t_i32).
Proof.
  destruct x as [x], y as [y].
  unfold U32.canonical, U32.raw, F32.width.
  unfold shift_defined, width, value, integer_u64, integer_i32,
    I32.value, I32.raw, I32.of_Z, S32.width, S32.signed.
  cbn; nia.
Qed.

Theorem multiply_reconstruction out1 out2 x y :
  U32.canonical x -> U32.canonical y ->
  let result := fq_mulx_u32 out1 out2 x y in
  U32.canonical (fst result) /\ U32.canonical (snd result) /\
  U32.raw (fst result) + 2^32 * U32.raw (snd result) = U32.raw x * U32.raw y.
Proof.
  intros Hx Hy. rewrite multiply_exact by assumption.
  destruct x as [x], y as [y].
  unfold U32.canonical, U32.raw, U32.of_Z, F32.width in *.
  cbn in *.
  assert (Hp : 0 <= x*y < 18446744073709551616) by nia.
  assert (Hq : 0 <= (x*y) / 4294967296 < 4294967296).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite (Z.mod_small ((x*y) / 4294967296) 4294967296) by lia.
  pose proof (Z.mod_pos_bound (x*y) 4294967296 ltac:(lia)).
  pose proof (Z.div_mod (x*y) 4294967296 ltac:(lia)).
  change (0 <= (x*y) mod 4294967296 < 4294967296 /\
    0 <= (x*y) / 4294967296 < 4294967296 /\
    (x*y) mod 4294967296 + 4294967296 * ((x*y) / 4294967296) = x*y).
  lia.
Qed.
