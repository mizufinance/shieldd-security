From Stdlib Require Import ZArith Lia List.
Open Scope Z_scope.

(* Finite integer semantics for the extracted arithmetic subset. Constructors
   are total; correspondence to Rust additionally requires canonical inputs. *)
Module Type FORMAT.
  Parameter width : Z.
  Parameter signed : bool.
End FORMAT.
Module Word (F : FORMAT).
  Inductive t := Word : Z -> t.
  Definition raw (x : t) := match x with Word z => z end.
  Definition of_Z (z : Z) := Word (z mod 2 ^ F.width).
  Definition value (x : t) :=
    let z := raw x in
    if andb F.signed (2 ^ (F.width - 1) <=? z) then z - 2 ^ F.width else z.
  Definition canonical (x : t) := 0 <= raw x < 2 ^ F.width.

  Lemma signed_value z :
    0 < F.width -> F.signed = true ->
    -2^(F.width-1) <= z < 2^(F.width-1) -> value (of_Z z) = z.
  Proof.
    intros Hw Hs Hz. unfold value, of_Z, raw. rewrite Hs. cbn [andb].
    assert (Hp : 0 < 2^(F.width-1)) by (apply Z.pow_pos_nonneg; lia).
    assert (Hb : 2^F.width = 2 * 2^(F.width-1)).
    { replace F.width with (Z.succ (F.width-1)) at 1 by lia.
      rewrite Z.pow_succ_r by lia. reflexivity. }
    destruct (Z_le_gt_dec 0 z).
    - rewrite Z.mod_small by lia.
      destruct (Z.leb_spec0 (2^(F.width-1)) z); lia.
    - assert (Hm : z mod 2^F.width = z + 2^F.width).
      { symmetry. apply Z.mod_unique with (q := -1); lia. }
      rewrite Hm. destruct (Z.leb_spec0 (2^(F.width-1)) (z+2^F.width)); lia.
  Qed.
End Word.
Module F8 <: FORMAT. Definition width := 8. Definition signed := false. End F8.
Module F32 <: FORMAT. Definition width := 32. Definition signed := false. End F32.
Module F64 <: FORMAT. Definition width := 64. Definition signed := false. End F64.
Module S8 <: FORMAT. Definition width := 8. Definition signed := true. End S8.
Module S64 <: FORMAT. Definition width := 64. Definition signed := true. End S64.
Module S32 <: FORMAT. Definition width := 32. Definition signed := true. End S32.
Module U8 := Word F8.
Module U32 := Word F32.
Module U64 := Word F64.
Module I32 := Word S32.
Module I8 := Word S8.
Module I64 := Word S64.
Declare Scope U8_scope.
Bind Scope U8_scope with U8.t.
Number Notation U8.t U8.of_Z U8.value : U8_scope.
Declare Scope U32_scope.
Bind Scope U32_scope with U32.t.
Number Notation U32.t U32.of_Z U32.value : U32_scope.
Declare Scope U64_scope.
Bind Scope U64_scope with U64.t.
Number Notation U64.t U64.of_Z U64.value : U64_scope.
Declare Scope I32_scope.
Bind Scope I32_scope with I32.t.
Number Notation I32.t I32.of_Z I32.value : I32_scope.
Declare Scope I8_scope.
Bind Scope I8_scope with I8.t.
Number Notation I8.t I8.of_Z I8.value : I8_scope.
Declare Scope I64_scope.
Bind Scope I64_scope with I64.t.
Number Notation I64.t I64.of_Z I64.value : I64_scope.
Definition t_u8 := U8.t.
Bind Scope U8_scope with t_u8.
Definition t_u32 := U32.t.
Bind Scope U32_scope with t_u32.
Definition t_u64 := U64.t.
Bind Scope U64_scope with t_u64.
Definition t_i32 := I32.t.
Bind Scope I32_scope with t_i32.

Definition t_i8 := I8.t.
Bind Scope I8_scope with t_i8.
Definition t_i64 := I64.t.
Bind Scope I64_scope with t_i64.
Definition t_usize := U64.t.
Bind Scope U64_scope with t_usize.

Class Integer (A : Type) := {
  width : Z;
  value : A -> Z;
  from_Z : Z -> A
}.
#[export] Instance integer_u8 : Integer t_u8 :=
  {| width := 8; value := U8.value; from_Z := U8.of_Z |}.
#[export] Instance integer_u32 : Integer t_u32 :=
  {| width := 32; value := U32.value; from_Z := U32.of_Z |}.
#[export] Instance integer_u64 : Integer t_u64 :=
  {| width := 64; value := U64.value; from_Z := U64.of_Z |}.
#[export] Instance integer_i32 : Integer t_i32 :=
  {| width := 32; value := I32.value; from_Z := I32.of_Z |}.
#[export] Instance integer_i8 : Integer t_i8 :=
  {| width := 8; value := I8.value; from_Z := I8.of_Z |}.
#[export] Instance integer_i64 : Integer t_i64 :=
  {| width := 64; value := I64.value; from_Z := I64.of_Z |}.
Definition cast {A B} `{Integer A} `{Integer B} (x : A) : B := from_Z (value x).
Definition f_add {A} `{Integer A} (x y : A) : A := from_Z (value x + value y).
Definition f_bitand {A} `{Integer A} (x y : A) : A := from_Z (Z.land (value x) (value y)).
(* Rust requires the shift count to be in range. The bridge theorem must prove
   this predicate; an invalid shift is not an admitted runtime operation. *)
Definition shift_defined {A B} `{Integer A} `{Integer B} (y : B) :=
  0 <= value y < @width A _.
Definition f_shr {A B} `{Integer A} `{Integer B} (x : A) (y : B) : A :=
  from_Z (Z.shiftr (value x) (value y)).

Definition f_sub {A} `{Integer A} (x y : A) : A := from_Z (value x - value y).
Definition f_mul {A} `{Integer A} (x y : A) : A := from_Z (value x * value y).
Definition f_not {A} `{Integer A} (x : A) : A := from_Z (Z.lnot (value x)).
Definition f_bitor {A} `{Integer A} (x y : A) : A := from_Z (Z.lor (value x) (value y)).

(* Array safety is a separate obligation: inputs have the declared length,
   and every access proves index_defined before using these total functions. *)
Definition t_Array (A : Type) (_ : t_usize) := list A.
Definition array_valid {A} (n : t_usize) (a : list A) :=
  U64.canonical n /\ Z.of_nat (length a) = U64.value n.
Definition index_defined {A} (a : list A) (i : t_usize) :=
  U64.canonical i /\ 0 <= U64.value i < Z.of_nat (length a).
Definition f_index {A} `{Integer A} (a : list A) (i : t_usize) : A :=
  nth (Z.to_nat (U64.value i)) a (from_Z 0).
Definition update_at_usize {A} (a : list A) (i : t_usize) (v : A) : list A :=
  firstn (Z.to_nat (U64.value i)) a ++ v :: skipn (S (Z.to_nat (U64.value i))) a.
