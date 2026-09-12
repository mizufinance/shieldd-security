From Stdlib Require Import ZArith Lia.
From Core Require Import Core.
From Slice Require Import Decaf_proof_slice_Fiat.
Open Scope Z_scope.

Theorem addcarry_exact out1 out2 carry x y :
  0 <= U8.raw carry <= 1 ->
  U32.canonical x -> U32.canonical y ->
  fq_addcarryx_u32 out1 out2 carry x y =
    (U32.of_Z (U8.raw carry + U32.raw x + U32.raw y),
     U8.of_Z ((U8.raw carry + U32.raw x + U32.raw y) / 2 ^ 32)).
Proof.
  destruct carry as [c], x as [x], y as [y].
  cbn [U8.raw U32.canonical U32.raw F32.width].
  intros Hc Hx Hy.
  unfold fq_addcarryx_u32, cast, f_add, f_bitand, f_shr.
  cbn [integer_u8 integer_u32 integer_u64 integer_i32 value from_Z
       U8.value U32.value U64.value I32.value U8.raw U32.raw U64.raw I32.raw
       U8.of_Z U32.of_Z U64.of_Z I32.of_Z F8.width F32.width F64.width S32.width
       F8.signed F32.signed F64.signed S32.signed].
  unfold U8.value, U32.value, U64.value, I32.value, U8.of_Z, U32.of_Z, U64.of_Z, I32.of_Z, U8.raw, U32.raw, U64.raw, I32.raw in *.
  cbn -[Z.shiftr] in *.
  unfold U32.canonical, U32.raw, F32.width in Hx, Hy; cbn in Hx, Hy.
  rewrite (Z.mod_small c 18446744073709551616) by lia.
  rewrite (Z.mod_small x 18446744073709551616) by lia.
  rewrite (Z.mod_small y 18446744073709551616) by lia.
  rewrite (Z.mod_small (c + x) 18446744073709551616) by lia.
  rewrite (Z.mod_small (c + x + y) 18446744073709551616) by lia.
  change 4294967295 with (Z.ones 32).
  rewrite Z.land_ones by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 32) with 4294967296.
  assert (Hr : 0 <= (c + x + y) mod 4294967296 < 4294967296)
    by (apply Z.mod_pos_bound; lia).
  assert (Hq : 0 <= (c + x + y) / 4294967296 < 2).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite (Z.mod_small ((c + x + y) mod 4294967296) 18446744073709551616) by lia.
  rewrite (Z.mod_small ((c + x + y) / 4294967296) 18446744073709551616) by lia.
  rewrite Z.mod_mod by lia.
  reflexivity.
Qed.

Theorem addcarry_safety carry x y :
  0 <= U8.raw carry <= 1 ->
  U32.canonical x -> U32.canonical y ->
  0 <= U8.raw carry + U32.raw x < 2 ^ 64 /\
  0 <= U8.raw carry + U32.raw x + U32.raw y < 2 ^ 64 /\
  @shift_defined t_u64 t_i32 integer_u64 integer_i32 (32 : t_i32).
Proof.
  destruct carry as [c], x as [x], y as [y].
  unfold U8.raw, U32.canonical, U32.raw, F32.width.
  unfold shift_defined, width, value, integer_u64, integer_i32,
    I32.value, I32.raw, I32.of_Z, S32.width, S32.signed.
  cbn; lia.
Qed.

Theorem addcarry_reconstruction out1 out2 carry x y :
  0 <= U8.raw carry <= 1 ->
  U32.canonical x -> U32.canonical y ->
  let result := fq_addcarryx_u32 out1 out2 carry x y in
  U32.canonical (fst result) /\
  0 <= U8.raw (snd result) <= 1 /\
  U32.raw (fst result) + 2 ^ 32 * U8.raw (snd result) =
    U8.raw carry + U32.raw x + U32.raw y.
Proof.
  intros Hc Hx Hy; rewrite addcarry_exact by assumption.
  destruct carry as [c], x as [x], y as [y].
  unfold U32.canonical, U32.raw, U8.raw, U32.of_Z, U8.of_Z,
    F32.width, F8.width in *; cbn in *.
  assert (Hq : 0 <= (c + x + y) / 4294967296 < 2).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite (Z.mod_small ((c + x + y) / 4294967296) 256) by lia.
  pose proof (Z.mod_pos_bound (c + x + y) 4294967296 ltac:(lia)).
  pose proof (Z.div_mod (c + x + y) 4294967296 ltac:(lia)).
  split; [exact H |].
  split; [lia |].
  change ((c + x + y) mod 4294967296 +
    4294967296 * ((c + x + y) / 4294967296) = c + x + y).
  lia.
Qed.
