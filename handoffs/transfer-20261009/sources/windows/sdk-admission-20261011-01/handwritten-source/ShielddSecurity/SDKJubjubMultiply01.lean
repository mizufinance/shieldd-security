import ShielddSecurity.SDKJubjubConcrete01
import ShielddSecurity.GroupScalarCodec

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.SDKJubjubMultiply01

local notation "F" => ConcreteJubjubField01.F
local notation "J" => ConcretePointTorsion01.curve.Point
local notation "d" => ConcreteJubjubField01.coefficient

/-- Mathematical source ConcreteCofactorModel01.model. Rust field and byte representation refinement
is separate; this model does not silently assert that refinement. -/
def identity : SDKJubjubExtended01.Extended F := SDKJubjubExtended01.affine Group.identityPoint

def zeroNiels : SDKJubjubExtended01.Niels F := ⟨1, 1, 1, 0⟩

theorem zero_niels : zeroNiels = SDKJubjubExtended01.toNiels d identity := by
  dsimp [zeroNiels, SDKJubjubExtended01.toNiels, identity,
    SDKJubjubExtended01.affine, Group.identityPoint]
  simp

def step (base acc : SDKJubjubExtended01.Extended F) (bit : Bool) :
    SDKJubjubExtended01.Extended F :=
  SDKJubjubExtended01.addNiels (SDKJubjubExtended01.double acc)
    (if bit then SDKJubjubExtended01.toNiels d base else zeroNiels)

def groupStep (base acc : J) (bit : Bool) : J :=
  2 • acc + (if bit then base else 0)

theorem identity_represents : SDKJubjubExtended01.Represents identity (ConcreteCofactorModel01.model.coordinates 0) := by
  rw [ConcreteCofactorModel01.model.identity]
  exact SDKJubjubExtended01.affine_represents Group.identityPoint

theorem step_represents (base acc : SDKJubjubExtended01.Extended F) (p q : J)
    (baseRep : SDKJubjubExtended01.Represents base (ConcreteCofactorModel01.model.coordinates p))
    (accRep : SDKJubjubExtended01.Represents acc (ConcreteCofactorModel01.model.coordinates q)) (bit : Bool) :
    SDKJubjubExtended01.Represents (step base acc bit) (ConcreteCofactorModel01.model.coordinates (groupStep p q bit)) := by
  cases bit with
  | false =>
      simp only [step, groupStep, Bool.false_eq_true, if_false, add_zero]
      rw [zero_niels]
      simpa only [add_zero] using SDKJubjubConcrete01.concrete_add _ _ (2 • q) 0
        (SDKJubjubConcrete01.concrete_double acc q accRep) identity_represents
  | true =>
      simp only [step, groupStep, if_true]
      exact SDKJubjubConcrete01.concrete_add _ _ (2 • q) p
        (SDKJubjubConcrete01.concrete_double acc q accRep) baseRep

theorem fold_represents (base acc : SDKJubjubExtended01.Extended F) (p q : J)
    (baseRep : SDKJubjubExtended01.Represents base (ConcreteCofactorModel01.model.coordinates p))
    (accRep : SDKJubjubExtended01.Represents acc (ConcreteCofactorModel01.model.coordinates q)) (bits : List Bool) :
    SDKJubjubExtended01.Represents (bits.foldl (step base) acc)
      (ConcreteCofactorModel01.model.coordinates (bits.foldl (groupStep p) q)) := by
  induction bits generalizing acc q with
  | nil => exact accRep
  | cons bit bits ih =>
      simp only [List.foldl_cons]
      exact ih _ _ (step_represents base acc p q baseRep accRep bit)

def value (base : J) : List Bool → J
  | [] => 0
  | bit :: bits => groupStep base (value base bits) bit

theorem reverse_loop (base : J) (bits : List Bool) :
    bits.reverse.foldl (groupStep base) 0 = value base bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, ih, value]

theorem value_binary (base : J) (bits : List Bool) : value base bits = binary bits • base := by
  induction bits with
  | nil => simp [value, binary]
  | cons bit bits ih =>
      cases bit <;> simp [value, groupStep, binary, ih, add_nsmul, mul_nsmul, add_comm]
      all_goals rw [← mul_nsmul, ← mul_nsmul, Nat.mul_comm]

def multiply (base : SDKJubjubExtended01.Extended F) (bits : List Bool) :
    SDKJubjubExtended01.Extended F := bits.reverse.foldl (step base) identity

theorem multiply_represents (base : SDKJubjubExtended01.Extended F) (p : J)
    (baseRep : SDKJubjubExtended01.Represents base (ConcreteCofactorModel01.model.coordinates p)) (bits : List Bool) :
    SDKJubjubExtended01.Represents (multiply base bits) (ConcreteCofactorModel01.model.coordinates (binary bits • p)) := by
  have result := fold_represents base identity p 0 baseRep identity_represents bits.reverse
  rw [reverse_loop, value_binary] at result
  exact result

def littleEndianByte (value index : Nat) : Nat := value / 2 ^ (8 * index) % 256

def encodedBit (value index : Nat) : Bool :=
  decide (littleEndianByte value (index / 8) / 2 ^ (index % 8) % 2 = 1)

theorem encoded_bit_formula (value index : Nat) :
    encodedBit value index = decide (value / 2 ^ index % 2 = 1) := by
  unfold encodedBit littleEndianByte
  rw [GroupScalarCodec.low_byte_bit _ _ (Nat.mod_lt _ (by decide)), Nat.div_div_eq_div_mul]
  have powers : 2 ^ (8 * (index / 8)) * 2 ^ (index % 8) = 2 ^ index := by
    rw [← pow_add]
    congr 1
    have division := Nat.mod_add_div index 8
    omega
  rw [powers]

/-- LSB order of the 252 bits retained by the SDK's reversed-byte,
reversed-inner-bit iterator after skip(4). Source iterator correspondence and
native byte representation remain independently reviewable boundaries. -/
def encodedBits (value : Nat) : List Bool := (List.range 252).map (encodedBit value)

theorem encoded_reader (value : Nat) : encodedBits value = GroupScalarCodec.readBits 252 value := by
  apply List.ext_getElem
  · simp [encodedBits, GroupScalarCodec.reader_length]
  · intro index leftBound rightBound
    have bound : index < 252 := by simpa [GroupScalarCodec.reader_length] using rightBound
    simp only [encodedBits, List.getElem_map, List.getElem_range]
    rw [encoded_bit_formula, GroupScalarCodec.reader_index 252 value index bound]

theorem canonical_multiply (base : SDKJubjubExtended01.Extended F) (p : J)
    (baseRep : SDKJubjubExtended01.Represents base (ConcreteCofactorModel01.model.coordinates p))
    (scalar : Nat) (bound : scalar < 2 ^ 252) :
    SDKJubjubExtended01.normalize (multiply base (encodedBits scalar)) =
      ConcreteCofactorModel01.model.coordinates (scalar • p) := by
  apply SDKJubjubExtended01.normalize_represents
  rw [encoded_reader]
  have result := multiply_represents base p baseRep (GroupScalarCodec.readBits 252 scalar)
  rw [GroupScalarCodec.reader_value 252 scalar bound] at result
  exact result

def modulusBytes : List Nat :=
  [183,44,247,214,94,14,151,208,130,16,200,204,147,32,104,166,
    0,59,52,1,1,59,103,6,169,175,51,101,234,180,125,14]

def littleEndianValue (bytes : List Nat) : Nat := bytes.foldr (fun byte acc => byte + 256 * acc) 0

theorem modulus_bytes_value : littleEndianValue modulusBytes = Scalar.order := by
  norm_num [littleEndianValue, modulusBytes, List.foldr, Scalar.order]

theorem modulus_test_iff (base : SDKJubjubExtended01.Extended F) (p : J)
    (baseRep : SDKJubjubExtended01.Represents base (ConcreteCofactorModel01.model.coordinates p)) :
    SDKJubjubExtended01.isIdentity (multiply base (encodedBits Scalar.order)) ↔ Scalar.order • p = 0 := by
  rw [encoded_reader]
  have represented := multiply_represents base p baseRep (encodedBits Scalar.order)
  rw [encoded_reader, GroupScalarCodec.reader_value 252 Scalar.order GroupScalarCodec.scalar_order_width] at represented
  rw [SDKJubjubExtended01.identity_test_iff _ _ represented, ← ConcreteCofactorModel01.model.identity]
  exact ConcreteCofactorModel01.model.injective.eq_iff

end ShielddSecurity.SDKJubjubMultiply01

set_option pp.all true in
#check @ShielddSecurity.SDKJubjubMultiply01.identity
#print axioms ShielddSecurity.SDKJubjubMultiply01.identity
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubMultiply01.zeroNiels
#print axioms ShielddSecurity.SDKJubjubMultiply01.zeroNiels
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubMultiply01.zero_niels
#print axioms ShielddSecurity.SDKJubjubMultiply01.zero_niels
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubMultiply01.step
#print axioms ShielddSecurity.SDKJubjubMultiply01.step
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubMultiply01.groupStep
#print axioms ShielddSecurity.SDKJubjubMultiply01.groupStep
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubMultiply01.identity_represents
#print axioms ShielddSecurity.SDKJubjubMultiply01.identity_represents
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubMultiply01.step_represents
#print axioms ShielddSecurity.SDKJubjubMultiply01.step_represents
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubMultiply01.fold_represents
#print axioms ShielddSecurity.SDKJubjubMultiply01.fold_represents
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubMultiply01.value
#print axioms ShielddSecurity.SDKJubjubMultiply01.value
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubMultiply01.reverse_loop
#print axioms ShielddSecurity.SDKJubjubMultiply01.reverse_loop
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubMultiply01.value_binary
#print axioms ShielddSecurity.SDKJubjubMultiply01.value_binary
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubMultiply01.multiply
#print axioms ShielddSecurity.SDKJubjubMultiply01.multiply
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubMultiply01.multiply_represents
#print axioms ShielddSecurity.SDKJubjubMultiply01.multiply_represents
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubMultiply01.littleEndianByte
#print axioms ShielddSecurity.SDKJubjubMultiply01.littleEndianByte
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubMultiply01.encodedBit
#print axioms ShielddSecurity.SDKJubjubMultiply01.encodedBit
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubMultiply01.encoded_bit_formula
#print axioms ShielddSecurity.SDKJubjubMultiply01.encoded_bit_formula
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubMultiply01.encodedBits
#print axioms ShielddSecurity.SDKJubjubMultiply01.encodedBits
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubMultiply01.encoded_reader
#print axioms ShielddSecurity.SDKJubjubMultiply01.encoded_reader
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubMultiply01.canonical_multiply
#print axioms ShielddSecurity.SDKJubjubMultiply01.canonical_multiply
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubMultiply01.modulusBytes
#print axioms ShielddSecurity.SDKJubjubMultiply01.modulusBytes
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubMultiply01.littleEndianValue
#print axioms ShielddSecurity.SDKJubjubMultiply01.littleEndianValue
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubMultiply01.modulus_bytes_value
#print axioms ShielddSecurity.SDKJubjubMultiply01.modulus_bytes_value
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubMultiply01.modulus_test_iff
#print axioms ShielddSecurity.SDKJubjubMultiply01.modulus_test_iff
