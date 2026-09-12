From Stdlib Require Import ZArith Lia.
From Core Require Import Core.
From Slice Require Import Decaf_proof_slice_Fiat.
Open Scope Z_scope.

Theorem borrow_exact out1 out2 carry x y :
  0 <= U8.raw carry <= 1 -> U32.canonical x -> U32.canonical y ->
  let difference := U32.raw x - U8.raw carry - U32.raw y in
  fq_subborrowx_u32 out1 out2 carry x y =
    (U32.of_Z difference, U8.of_Z (if difference <? 0 then 1 else 0)).
Proof.
  destruct carry as [c], x as [x], y as [y].
  unfold U8.raw, U32.raw, U32.canonical, F32.width. intros Hc Hx Hy.
  cbn zeta.
  unfold fq_subborrowx_u32, cast, f_sub, f_bitand, f_shr.
  cbn [integer_u8 integer_u32 integer_i8 integer_i32 integer_i64 value from_Z
       U8.value U32.value U8.raw U32.raw F8.signed F32.signed].
  unfold U32.value, U8.value, U32.raw, U8.raw, F32.signed, F8.signed in *.
  cbn [andb] in *.
  change (I64.value (4294967295 : t_i64)) with 4294967295.
  change (I32.value (32 : t_i32)) with 32.
  change (I8.value (0 : t_i8)) with 0.
  rewrite (I64.signed_value x) by (try reflexivity; cbn; lia).
  rewrite (I64.signed_value c) by (try reflexivity; cbn; lia).
  rewrite (I64.signed_value y) by (try reflexivity; cbn; lia).
  rewrite (I64.signed_value (x-c)) by (try reflexivity; cbn; lia).
  rewrite (I64.signed_value (x-c-y)) by (try reflexivity; cbn; lia).
  change 4294967295 with (Z.ones 32).
  rewrite Z.land_ones, Z.shiftr_div_pow2 by lia.
  assert (Hr : 0 <= (x-c-y) mod 2^32 < 2^32) by (apply Z.mod_pos_bound; lia).
  rewrite (I64.signed_value ((x-c-y) mod 2^32)) by (try reflexivity; cbn in *; lia).
  assert (Hq : -1 <= (x-c-y) / 2^32 < 1).
  { split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite (I64.signed_value ((x-c-y) / 2^32)) by (try reflexivity; cbn in *; lia).
  rewrite (I8.signed_value ((x-c-y) / 2^32)) by (try reflexivity; cbn in *; lia).
  rewrite (I8.signed_value (0-(x-c-y) / 2^32)) by (try reflexivity; cbn in *; lia).
  assert (Hlow : U32.of_Z ((x-c-y) mod 2^32) = U32.of_Z (x-c-y)).
  { unfold U32.of_Z, F32.width. rewrite Z.mod_mod by lia. reflexivity. }
  rewrite Hlow.
  destruct (Z.ltb_spec0 (x-c-y) 0) as [Hneg|Hpos].
  - assert (Hdiv : (x-c-y) / 2^32 = -1).
    { symmetry. apply Z.div_unique with (r := x-c-y+2^32); lia. }
    rewrite Hdiv. reflexivity.
  - rewrite Z.div_small by lia. reflexivity.
Qed.

Theorem borrow_safety carry x y :
  0 <= U8.raw carry <= 1 -> U32.canonical x -> U32.canonical y ->
  let first := U32.raw x - U8.raw carry in
  let difference := first - U32.raw y in
  -2^63 <= first < 2^63 /\ -2^63 <= difference < 2^63 /\
  -1 <= difference / 2^32 < 1 /\ 0 <= -(difference / 2^32) <= 1 /\
  @shift_defined t_i64 t_i32 integer_i64 integer_i32 (32 : t_i32).
Proof.
  destruct carry as [c], x as [x], y as [y].
  unfold U8.raw, U32.canonical, U32.raw, F32.width.
  cbn zeta. intros Hc Hx Hy.
  assert (Hq : -1 <= (x-c-y) / 2^32 < 1).
  { split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]. }
  unfold shift_defined, width, value, integer_i64, integer_i32,
    I32.value, I32.raw, I32.of_Z, S32.width, S32.signed.
  cbn in *; lia.
Qed.

Theorem borrow_reconstruction out1 out2 carry x y :
  0 <= U8.raw carry <= 1 -> U32.canonical x -> U32.canonical y ->
  let result := fq_subborrowx_u32 out1 out2 carry x y in
  U32.canonical (fst result) /\ 0 <= U8.raw (snd result) <= 1 /\
  U32.raw (fst result) - 2^32 * U8.raw (snd result) =
    U32.raw x - U8.raw carry - U32.raw y.
Proof.
  intros Hc Hx Hy. rewrite borrow_exact by assumption.
  destruct carry as [c], x as [x], y as [y].
  unfold U32.canonical, U32.raw, U8.raw, F32.width in *.
  cbn zeta. cbn [U32.raw U8.raw] in *.
  destruct (Z.ltb_spec0 (x-c-y) 0) as [Hneg|Hpos].
  - assert (Hm : (x-c-y) mod 2^32 = x-c-y+2^32).
    { symmetry. apply Z.mod_unique with (q := -1); lia. }
    unfold U32.of_Z, U8.of_Z, U32.raw, U8.raw, F32.width, F8.width.
    cbn. change (2^32) with 4294967296 in Hm. rewrite Hm. lia.
  - unfold U32.of_Z, U8.of_Z, U32.raw, U8.raw, F32.width, F8.width.
    cbn. rewrite Z.mod_small by lia. lia.
Qed.
