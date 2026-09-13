(* Correspondence of native Rust32 helpers with Fiat's interpreted primitives.
   These lemmas do not yet compose the full native multiplication body. *)
From Stdlib Require Import ZArith Lia.
Require Import Crypto.Language.PreExtra.
Require Import Crypto.Util.ZRange.Operations.
From Core Require Import Core RustMultiply Carry RustBorrow RustSelect.
From Slice Require Import Decaf_proof_slice_Fiat.
Open Scope Z_scope.
Local Transparent PreExtra.ident.cast PreExtra.ident.cast2.

Definition unsigned32 : ZRange.zrange :=
  {| ZRange.lower := 0; ZRange.upper := 4294967295 |}.
Definition bit_range : ZRange.zrange :=
  {| ZRange.lower := 0; ZRange.upper := 1 |}.

Theorem fiat_cast32 z :
  PreExtra.ident.cast unsigned32 z = z mod 4294967296.
Proof.
  change ((if (0 <=? z) && (z <=? 4294967295)
           then z else (z - 0) mod 4294967296 + 0) = z mod 4294967296).
  rewrite Z.sub_0_r, Z.add_0_r.
  destruct (Z.leb_spec0 0 z); destruct (Z.leb_spec0 z 4294967295); cbn.
  - symmetry. apply Z.mod_small. lia.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem fiat_cast_bit z :
  0 <= z <= 1 -> PreExtra.ident.cast bit_range z = z.
Proof.
  intros Hz.
  change ((if (0 <=? z) && (z <=? 1)
           then z else (z - 0) mod 2 + 0) = z).
  rewrite (proj2 (Z.leb_le 0 z)) by lia.
  rewrite (proj2 (Z.leb_le z 1)) by lia.
  reflexivity.
Qed.

Theorem multiply_fiat out1 out2 x y :
  U32.canonical x -> U32.canonical y ->
  let native := fq_mulx_u32 out1 out2 x y in
  (U32.raw (fst native), U32.raw (snd native)) =
  PreExtra.ident.cast2 (unsigned32, unsigned32)
    (Definitions.Z.mul_split 4294967296 (U32.raw x) (U32.raw y)).
Proof.
  intros Hx Hy. rewrite multiply_exact by assumption.
  unfold PreExtra.ident.cast2.
  cbn [fst snd]. rewrite !fiat_cast32.
  change (((U32.raw x * U32.raw y) mod 4294967296,
           ((U32.raw x * U32.raw y) / 4294967296) mod 4294967296) =
          ((Z.land (U32.raw x * U32.raw y) (Z.ones 32)) mod 4294967296,
           (Z.shiftr (U32.raw x * U32.raw y) 32) mod 4294967296)).
  rewrite Z.land_ones, Z.shiftr_div_pow2 by lia.
  change (2^32) with 4294967296.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Theorem addcarry_fiat out1 out2 c x y :
  0 <= U8.raw c <= 1 -> U32.canonical x -> U32.canonical y ->
  let native := fq_addcarryx_u32 out1 out2 c x y in
  (U32.raw (fst native), U8.raw (snd native)) =
  PreExtra.ident.cast2 (unsigned32, bit_range)
    (Definitions.Z.add_with_get_carry_full 4294967296
       (U8.raw c) (U32.raw x) (U32.raw y)).
Proof.
  intros Hc Hx Hy. rewrite addcarry_exact by assumption.
  assert (Hq : 0 <= (U8.raw c + U32.raw x + U32.raw y) / 4294967296 <= 1).
  { unfold U32.canonical, F32.width in Hx, Hy.
    assert (Hlt : (U8.raw c + U32.raw x + U32.raw y) / 4294967296 < 2).
    { apply Z.div_lt_upper_bound; cbn in *; lia. }
    split; [apply Z.div_pos; cbn in *; lia | lia]. }
  unfold PreExtra.ident.cast2. cbn [fst snd].
  change (((U8.raw c + U32.raw x + U32.raw y) mod 4294967296,
           ((U8.raw c + U32.raw x + U32.raw y) / 4294967296) mod 256) =
          (PreExtra.ident.cast unsigned32
             ((U8.raw c + U32.raw x + U32.raw y) mod 4294967296),
           PreExtra.ident.cast bit_range
             ((U8.raw c + U32.raw x + U32.raw y) / 4294967296))).
  rewrite fiat_cast32, fiat_cast_bit by assumption.
  rewrite Z.mod_mod by lia.
  rewrite (Z.mod_small ((U8.raw c + U32.raw x + U32.raw y) / 4294967296) 256) by lia.
  reflexivity.
Qed.

Theorem select_fiat out c x y :
  0 <= U8.raw c <= 1 -> U32.canonical x -> U32.canonical y ->
  U32.raw (fq_cmovznz_u32 out c x y) =
  PreExtra.ident.cast unsigned32
    (Definitions.Z.zselect (U8.raw c) (U32.raw x) (U32.raw y)).
Proof.
  intros Hc Hx Hy. rewrite select_exact by assumption.
  unfold Definitions.Z.zselect.
  destruct (U8.raw c =? 0); rewrite fiat_cast32;
    symmetry; apply Z.mod_small; assumption.
Qed.

Theorem borrow_fiat out1 out2 c x y :
  0 <= U8.raw c <= 1 -> U32.canonical x -> U32.canonical y ->
  let native := fq_subborrowx_u32 out1 out2 c x y in
  (U32.raw (fst native), U8.raw (snd native)) =
  PreExtra.ident.cast2 (unsigned32, bit_range)
    (Definitions.Z.sub_with_get_borrow_full 4294967296
       (U8.raw c) (U32.raw x) (U32.raw y)).
Proof.
  intros Hc Hx Hy.
  pose proof (borrow_reconstruction out1 out2 c x y Hc Hx Hy) as H.
  destruct (fq_subborrowx_u32 out1 out2 c x y) as [lo hi].
  cbn [fst snd] in H |- *. destruct H as [Hlo [Hhi Heq]].
  unfold U32.canonical, F32.width in Hlo.
  change (2^32) with 4294967296 in Heq, Hlo.
  unfold PreExtra.ident.cast2. cbn [fst snd].
  change ((U32.raw lo, U8.raw hi) =
    (PreExtra.ident.cast unsigned32
       ((-U8.raw c + U32.raw x + -U32.raw y) mod 4294967296),
     PreExtra.ident.cast bit_range
       (-((-U8.raw c + U32.raw x + -U32.raw y) / 4294967296)))).
  assert (Hm : (-U8.raw c + U32.raw x + -U32.raw y) mod 4294967296 = U32.raw lo).
  { symmetry. apply Z.mod_unique with (q := -U8.raw hi); lia. }
  assert (Hd : (-U8.raw c + U32.raw x + -U32.raw y) / 4294967296 = -U8.raw hi).
  { symmetry. apply Z.div_unique with (r := U32.raw lo); lia. }
  rewrite Hm, Hd, Z.opp_involutive, fiat_cast32, fiat_cast_bit by assumption.
  rewrite Z.mod_small by assumption. reflexivity.
Qed.

(* The inline additions in the multiplication body add a carry to a product's
   high word, or add two carries. Ordinary word canonicality alone would not
   justify the first addition without this stronger high-word bound. *)
Theorem multiply_high_room out1 out2 x y :
  U32.canonical x -> U32.canonical y ->
  0 <= U32.raw (snd (fq_mulx_u32 out1 out2 x y)) < 4294967295.
Proof.
  intros Hx Hy. rewrite multiply_exact by assumption.
  unfold U32.canonical, F32.width in Hx, Hy.
  assert (Hp : 0 <= U32.raw x * U32.raw y < 4294967296 * 4294967295)
    by (cbn in *; nia).
  assert (Hq : 0 <= (U32.raw x * U32.raw y) / 4294967296 < 4294967295).
  { split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
  change (0 <= ((U32.raw x * U32.raw y) / 4294967296) mod 4294967296 < 4294967295).
  rewrite Z.mod_small by lia. exact Hq.
Qed.

Theorem carry_high_add out1 out2 c x y :
  0 <= U8.raw c <= 1 -> U32.canonical x -> U32.canonical y ->
  let high := snd (fq_mulx_u32 out1 out2 x y) in
  0 <= U8.raw c + U32.raw high < 4294967296 /\
  U32.raw (f_add (cast c : t_u32) high) = U8.raw c + U32.raw high.
Proof.
  intros Hc Hx Hy.
  pose proof (multiply_high_room out1 out2 x y Hx Hy) as Hhigh.
  cbn zeta. split; [lia|].
  change (((U8.raw c mod 4294967296 + U32.raw (snd (fq_mulx_u32 out1 out2 x y)))
             mod 4294967296) = U8.raw c + U32.raw (snd (fq_mulx_u32 out1 out2 x y))).
  rewrite (Z.mod_small (U8.raw c) 4294967296) by lia.
  apply Z.mod_small. lia.
Qed.

Theorem carry_carry_add c d :
  0 <= U8.raw c <= 1 -> 0 <= U8.raw d <= 1 ->
  0 <= U8.raw c + U8.raw d < 4294967296 /\
  U32.raw (f_add (cast c : t_u32) (cast d : t_u32)) = U8.raw c + U8.raw d.
Proof.
  intros Hc Hd. split; [lia|].
  change (((U8.raw c mod 4294967296 + U8.raw d mod 4294967296) mod 4294967296)
            = U8.raw c + U8.raw d).
  rewrite (Z.mod_small (U8.raw c) 4294967296),
          (Z.mod_small (U8.raw d) 4294967296) by lia.
  apply Z.mod_small. lia.
Qed.
