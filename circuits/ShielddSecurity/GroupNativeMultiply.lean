import ShielddSecurity.GroupExtended
import ShielddSecurity.GroupFixedWindows

set_option maxHeartbeats 300000

namespace ShielddSecurity.GroupNativeMultiply

open Group

variable {F : Type} [Field F]

/-- The owned native `multiply` loop is at shieldd.lock
844389ee069e1fb2e576708842d0b389b4d9a44a, group.rs lines 74-101 (SHA256
ca75207acfd6bcb794f9f54b8ab3f52b236478f6b10761d459747dcbb9155971).
This Boolean view of its inputs converts each bit to field zero/one. The actual
field-bit list, upstream scalar encoding and 255-bit extraction are separate
source/codec obligations; arbitrary field elements are not treated as bits. -/
def pairBits : List Bool → List (Bool × Bool)
  | [] => []
  | [low] => [(low, false)]
  | low :: high :: rest => (low, high) :: pairBits rest

def pairDigit (pair : Bool × Bool) : Nat :=
  pair.1.toNat + 2 * pair.2.toNat

/-- Odd final chunks have high=false, matching the native default field zero.
Chunk digits are derived from the bit list rather than supplied as a trace. -/
theorem pair_bits_digits (bits : List Bool) :
    (pairBits bits).map pairDigit = TransferWindows.pairDigits bits := by
  match bits with
  | [] => rfl
  | [low] => cases low <;> rfl
  | low :: high :: rest =>
    simp only [pairBits, List.map_cons, pairDigit, TransferWindows.pairDigits]
    rw [pair_bits_digits rest]
    cases low <;> cases high <;> rfl
termination_by structural bits

theorem pair_bits_order (bits : List Bool) :
    (pairBits bits).reverse.map pairDigit = (TransferWindows.pairDigits bits).reverse := by
  rw [List.map_reverse, pair_bits_digits]

/-- Reuse the existing reversed radix-four loop and binary reconstruction.
Neither the number of windows nor a fixed-width constraint walk is unrolled. -/
theorem pair_loop_value {J : Type} [AddCommGroup J] (base : J) (bits : List Bool) :
    (pairBits bits).reverse.foldl
      (fun acc pair => 4 • acc + pairDigit pair • base) 0 =
      ShielddSecurity.binary bits • base := by
  calc
    _ = ((pairBits bits).map pairDigit).reverse.foldl
        (fun acc digit => 4 • acc + digit • base) 0 := by
      rw [← List.map_reverse, List.foldl_map]
    _ = _ := by
      rw [pair_bits_digits, TransferWindows.variable_loop, TransferWindows.variable_value,
        TransferWindows.pair_digits_value]

/-- Exactly two native Extended doubles, selection, affine lift and add. -/
def nativeStep (d : F) (base twice triple : Point F) (value : GroupExtended.Extended F)
    (pair : Bool × Bool) : GroupExtended.Extended F :=
  GroupExtended.add d (GroupExtended.double (GroupExtended.double value))
    (GroupExtended.affine
      (windowPoint (if pair.1 then 1 else 0) (if pair.2 then 1 else 0) base twice triple))

/-- Tables are computed once; the native iterator visits reversed ascending
chunks, starts at Extended(identity), and normalizes only after the loop. -/
def multiplyExtended (d : F) (base : Point F) (bits : List Bool) : GroupExtended.Extended F :=
  let twice := GroupFixedWindows.nativeAdd d base base
  let triple := GroupFixedWindows.nativeAdd d twice base
  (pairBits bits).reverse.foldl (nativeStep d base twice triple)
    (GroupExtended.affine identityPoint)

def nativeMultiply (d : F) (base : Point F) (bits : List Bool) : Point F :=
  GroupExtended.normalize (multiplyExtended d base bits)

theorem native_precompute_coordinates {J : Type} [AddCommGroup J]
    (d imaginary : F) (model : StandardCurveModel J d) (nonSquare : NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (base : J) :
    GroupFixedWindows.nativeAdd d (model.coordinates base) (model.coordinates base) =
        model.coordinates (2 • base) ∧
    GroupFixedWindows.nativeAdd d
        (GroupFixedWindows.nativeAdd d (model.coordinates base) (model.coordinates base))
        (model.coordinates base) = model.coordinates (3 • base) := by
  have twiceEqual : GroupFixedWindows.nativeAdd d
      (model.coordinates base) (model.coordinates base) = model.coordinates (2 • base) := by
    rw [GroupFixedWindows.native_add_coordinates d imaginary model nonSquare imaginarySquare,
      two_nsmul]
  refine ⟨twiceEqual, ?_⟩
  rw [twiceEqual,
    GroupFixedWindows.native_add_coordinates d imaginary model nonSquare imaginarySquare]
  have count : 2 • base + base = (3 : Nat) • base := by
    simp only [show (3 : Nat) = 2 + 1 from rfl, add_nsmul, one_nsmul]
  exact congrArg model.coordinates count

/-- Standard-model curve validity supplies the double invariant's premise.
The conclusion retains nonzero Z and T=xyZ through the full operation. -/
theorem extended_double_coordinates {J : Type} [AddCommGroup J]
    (d imaginary : F) (model : StandardCurveModel J d) (nonSquare : NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (value : GroupExtended.Extended F)
    (point : J) (represented : GroupExtended.Represents value (model.coordinates point)) :
    GroupExtended.Represents (GroupExtended.double value) (model.coordinates (2 • point)) := by
  rw [two_nsmul, model.addition]
  exact (GroupExtended.double_represents d imaginary nonSquare imaginarySquare value
    (model.coordinates point) represented (model.onCurve point)).1

theorem extended_add_coordinates {J : Type} [AddCommGroup J]
    (d imaginary : F) (model : StandardCurveModel J d) (nonSquare : NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (two : (2 : F) ≠ 0)
    (left right : GroupExtended.Extended F) (p q : J)
    (leftRep : GroupExtended.Represents left (model.coordinates p))
    (rightRep : GroupExtended.Represents right (model.coordinates q)) :
    GroupExtended.Represents (GroupExtended.add d left right) (model.coordinates (p + q)) := by
  rw [model.addition]
  exact GroupExtended.add_represents d imaginary nonSquare imaginarySquare two
    left right (model.coordinates p) (model.coordinates q) leftRep rightRep
    (model.onCurve p) (model.onCurve q)

theorem native_step_represents {J : Type} [AddCommGroup J]
    (d imaginary : F) (model : StandardCurveModel J d) (nonSquare : NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (two : (2 : F) ≠ 0)
    (value : GroupExtended.Extended F) (acc base : J) (pair : Bool × Bool)
    (represented : GroupExtended.Represents value (model.coordinates acc)) :
    GroupExtended.Represents
      (nativeStep d (model.coordinates base) (model.coordinates (2 • base))
        (model.coordinates (3 • base)) value pair)
      (model.coordinates (4 • acc + pairDigit pair • base)) := by
  have first := extended_double_coordinates d imaginary model nonSquare imaginarySquare
    value acc represented
  have second := extended_double_coordinates d imaginary model nonSquare imaginarySquare
    (GroupExtended.double value) (2 • acc) first
  unfold nativeStep
  rw [TransferOwnership.selected_coordinates d model base pair.1 pair.2]
  have added := extended_add_coordinates d imaginary model nonSquare imaginarySquare two
    (GroupExtended.double (GroupExtended.double value))
    (GroupExtended.affine (model.coordinates (pairDigit pair • base)))
    (2 • (2 • acc)) (pairDigit pair • base) second
    (GroupExtended.affine_represents (model.coordinates (pairDigit pair • base)))
  simpa only [← mul_nsmul] using added

/-- Symbolic list induction transports the exact Extended operations through
the represented accumulator. No desired output or scalar equality is assumed. -/
theorem native_loop_represents {J : Type} [AddCommGroup J]
    (d imaginary : F) (model : StandardCurveModel J d) (nonSquare : NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (two : (2 : F) ≠ 0)
    (pairs : List (Bool × Bool)) (value : GroupExtended.Extended F) (acc base : J)
    (represented : GroupExtended.Represents value (model.coordinates acc)) :
    GroupExtended.Represents
      (pairs.foldl (nativeStep d (model.coordinates base) (model.coordinates (2 • base))
        (model.coordinates (3 • base))) value)
      (model.coordinates
        (pairs.foldl (fun current pair => 4 • current + pairDigit pair • base) acc)) := by
  induction pairs generalizing value acc with
  | nil => exact represented
  | cons pair tail ih =>
    have step := native_step_represents d imaginary model nonSquare imaginarySquare
      two value acc base pair represented
    simpa only [List.foldl_cons] using
      ih (value := nativeStep d (model.coordinates base) (model.coordinates (2 • base))
            (model.coordinates (3 • base)) value pair)
        (acc := 4 • acc + pairDigit pair • base) step

/-- Local native multiplication computes the bit-defined scalar, retaining
the complete Extended invariant before final normalization. Boolean inputs,
field operations and the explicit standard curve model are the contracts. -/
theorem native_multiply_represents {J : Type} [AddCommGroup J]
    (d imaginary : F) (model : StandardCurveModel J d) (nonSquare : NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (two : (2 : F) ≠ 0)
    (base : J) (bits : List Bool) :
    GroupExtended.Represents (multiplyExtended d (model.coordinates base) bits)
      (model.coordinates (ShielddSecurity.binary bits • base)) := by
  have precomputed := native_precompute_coordinates d imaginary model nonSquare imaginarySquare base
  dsimp only [multiplyExtended]
  rw [precomputed.2, precomputed.1]
  have initial : GroupExtended.Represents (GroupExtended.affine (identityPoint : Point F))
      (model.coordinates (0 : J)) := by
    rw [model.identity]
    exact GroupExtended.affine_represents identityPoint
  have loop := native_loop_represents d imaginary model nonSquare imaginarySquare two
    (pairBits bits).reverse (GroupExtended.affine identityPoint) 0 base initial
  rw [pair_loop_value] at loop
  exact loop

/-- The actual final inverse has a proved nonzero argument, for every bit
length including empty and odd lists; no timeout or fixed 126-step replay is
part of the statement. -/
theorem native_multiply_denominator_nonzero {J : Type} [AddCommGroup J]
    (d imaginary : F) (model : StandardCurveModel J d) (nonSquare : NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (two : (2 : F) ≠ 0)
    (base : J) (bits : List Bool) :
    (multiplyExtended d (model.coordinates base) bits).z ≠ 0 :=
  (native_multiply_represents d imaginary model nonSquare imaginarySquare two base bits).1

/-- Final normalization discharges the exact formal native loop's operation
contract. This neither certifies the runtime field/codec implementation nor
instantiates the standard curve model or joins compiled caller/row evidence. -/
theorem native_multiply_coordinates {J : Type} [AddCommGroup J]
    (d imaginary : F) (model : StandardCurveModel J d) (nonSquare : NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (two : (2 : F) ≠ 0)
    (base : J) (bits : List Bool) :
    nativeMultiply d (model.coordinates base) bits =
      model.coordinates (ShielddSecurity.binary bits • base) := by
  exact GroupExtended.normalize_represents _ _
    (native_multiply_represents d imaginary model nonSquare imaginarySquare two base bits)

set_option pp.all true in
#check @pair_bits_digits
#print axioms pair_bits_digits
set_option pp.all true in
#check @pair_bits_order
#print axioms pair_bits_order
set_option pp.all true in
#check @pair_loop_value
#print axioms pair_loop_value
set_option pp.all true in
#check @native_precompute_coordinates
#print axioms native_precompute_coordinates
set_option pp.all true in
#check @extended_double_coordinates
#print axioms extended_double_coordinates
set_option pp.all true in
#check @extended_add_coordinates
#print axioms extended_add_coordinates
set_option pp.all true in
#check @native_step_represents
#print axioms native_step_represents
set_option pp.all true in
#check @native_loop_represents
#print axioms native_loop_represents
set_option pp.all true in
#check @native_multiply_represents
#print axioms native_multiply_represents
set_option pp.all true in
#check @native_multiply_denominator_nonzero
#print axioms native_multiply_denominator_nonzero
set_option pp.all true in
#check @native_multiply_coordinates
#print axioms native_multiply_coordinates

end ShielddSecurity.GroupNativeMultiply
