import ShielddSecurity.TransferScalarPackChunk01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarPackWalk01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferScalarLittleEndianBytes01 (decodeLE)
open TransferScalarPackChunk01
/-! Source-shaped chunks(31)/map/collect recurrence over every finite typed
byte list. Each chunk derives decoder acceptance and exact field meaning;
ordered concatenation recovers input. Equal field lists determine the exact
input when its length is bound, as required by the source pack documentation.
This proves packing values/order, not hash collision resistance. Native slice
iterator/Vec/collect/allocator/copy/compiler/ABI/caller binding remains open. -/

def source31ByteChunks : (bytes : List UInt8) → List { chunk : List UInt8 // chunk.length ≤ 31 }
  | [] => []
  | byte :: rest =>
    ⟨(byte :: rest).take 31, by rw [List.length_take]; exact Nat.min_le_left _ _⟩ ::
      source31ByteChunks ((byte :: rest).drop 31)
termination_by bytes => bytes.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  omega

def sourcePackByteFields (bytes : List UInt8) : List CanonicalScalar :=
  (source31ByteChunks bytes).map (fun chunk => sourcePackedChunkField chunk.val chunk.property)

theorem every_source_pack_walk_chunk_derives_success_choice_one
    (bytes : List UInt8) :
    (source31ByteChunks bytes).all (fun chunk =>
      TransferScalarChoiceBit01.sourceCanonicalChoiceByte (sourcePaddedChunkBytes chunk.val chunk.property) == 1) = true := by
  apply List.all_eq_true.mpr
  intro chunk _
  rw [every_source_packed_chunk_derives_the_exact_success_choice_byte]
  rfl

theorem generic_mapped_list_composition_preserves_pointwise_values
    {α β γ : Type} (first : α → β) (second : β → γ) (expected : α → γ)
    (pointwise : ∀ value, second (first value) = expected value) (values : List α) :
    (values.map first).map second = values.map expected := by
  rw [List.map_map]
  apply List.map_congr_left
  intro value _
  exact pointwise value

theorem complete_source_pack_walk_has_exact_ordered_chunk_integer_field_values (bytes : List UInt8) :
    (sourcePackByteFields bytes).map (fun scalar : CanonicalScalar => montgomeryValue scalar.words) =
      (source31ByteChunks bytes).map (fun chunk => decodeLE chunk.val) := by
  exact generic_mapped_list_composition_preserves_pointwise_values
    (fun chunk : { chunk : List UInt8 // chunk.length ≤ 31 } => sourcePackedChunkField chunk.val chunk.property)
    (fun scalar : CanonicalScalar => montgomeryValue scalar.words)
    (fun chunk => decodeLE chunk.val)
    (fun chunk => every_source_packed_chunk_has_the_exact_original_mathematical_integer chunk.val chunk.property)
    (source31ByteChunks bytes)

theorem complete_source31_byte_chunk_walk_preserves_exact_input_order (bytes : List UInt8) :
    ((source31ByteChunks bytes).map (fun chunk => chunk.val)).flatten = bytes := by
  have all : ∀ count, ∀ input : List UInt8, input.length = count →
      ((source31ByteChunks input).map (fun chunk => chunk.val)).flatten = input := by
    intro count
    induction count using Nat.strongRecOn with
    | ind count ih =>
      intro input size
      cases input with
      | nil => rw [source31ByteChunks]; rfl
      | cons byte rest =>
        have smaller : ((byte :: rest).drop 31).length < count := by
          rw [List.length_drop, List.length_cons]
          simp only [List.length_cons] at size
          omega
        have tail := ih _ smaller ((byte :: rest).drop 31) rfl
        rw [source31ByteChunks]
        change (byte :: rest).take 31 ++
          ((source31ByteChunks ((byte :: rest).drop 31)).map (fun chunk => chunk.val)).flatten = byte :: rest
        rw [tail]
        exact List.take_append_drop 31 (byte :: rest)
  exact all bytes.length bytes rfl

theorem complete_source_byte_packing_is_injective_when_exact_input_length_is_bound
    (left right : List UInt8) (sameLength : left.length = right.length)
    (sameFields : (sourcePackByteFields left).map (fun scalar : CanonicalScalar => montgomeryValue scalar.words) =
      (sourcePackByteFields right).map (fun scalar : CanonicalScalar => montgomeryValue scalar.words)) : left = right := by
  rw [complete_source_pack_walk_has_exact_ordered_chunk_integer_field_values,
    complete_source_pack_walk_has_exact_ordered_chunk_integer_field_values] at sameFields
  have all : ∀ count, ∀ a b : List UInt8, a.length = count → a.length = b.length →
      (source31ByteChunks a).map (fun chunk => decodeLE chunk.val) =
        (source31ByteChunks b).map (fun chunk => decodeLE chunk.val) → a = b := by
    intro count
    induction count using Nat.strongRecOn with
    | ind count ih =>
      intro a b size lengths values
      cases a with
      | nil =>
        have empty : b = [] := List.eq_nil_of_length_eq_zero lengths.symm
        exact empty.symm
      | cons byte rest =>
        cases b with
        | nil => simp only [List.length_cons, List.length_nil] at lengths; omega
        | cons other tail =>
          rw [source31ByteChunks, source31ByteChunks] at values
          change decodeLE ((byte :: rest).take 31) ::
            (source31ByteChunks ((byte :: rest).drop 31)).map (fun chunk => decodeLE chunk.val) =
              decodeLE ((other :: tail).take 31) ::
                (source31ByteChunks ((other :: tail).drop 31)).map (fun chunk => decodeLE chunk.val) at values
          have heads : decodeLE ((byte :: rest).take 31) = decodeLE ((other :: tail).take 31) := List.cons.inj values |>.1
          have tails := List.cons.inj values |>.2
          have prefixWidths : ((byte :: rest).take 31).length = ((other :: tail).take 31).length := by
            rw [List.length_take, List.length_take, lengths]
          have prefixes := TransferScalarByteEquality01.typed_little_endian_decoder_is_injective_at_equal_width
            ((byte :: rest).take 31) ((other :: tail).take 31) prefixWidths heads
          have smaller : ((byte :: rest).drop 31).length < count := by
            rw [List.length_drop, List.length_cons]
            simp only [List.length_cons] at size
            omega
          have tailWidths : ((byte :: rest).drop 31).length = ((other :: tail).drop 31).length := by
            rw [List.length_drop, List.length_drop, lengths]
          have tailSame := ih _ smaller ((byte :: rest).drop 31) ((other :: tail).drop 31) rfl tailWidths tails
          have joined := (congrArg (fun chunkPrefix : List UInt8 => chunkPrefix ++ (byte :: rest).drop 31) prefixes).trans
            (congrArg (List.append ((other :: tail).take 31)) tailSame)
          exact (List.take_append_drop 31 (byte :: rest)).symm.trans
            (joined.trans (List.take_append_drop 31 (other :: tail)))
  exact all left.length left right rfl sameLength sameFields

set_option pp.all true in
#check @source31ByteChunks
#print axioms source31ByteChunks
set_option pp.all true in
#check @sourcePackByteFields
#print axioms sourcePackByteFields
set_option pp.all true in
#check @every_source_pack_walk_chunk_derives_success_choice_one
#print axioms every_source_pack_walk_chunk_derives_success_choice_one
set_option pp.all true in
#check @generic_mapped_list_composition_preserves_pointwise_values
#print axioms generic_mapped_list_composition_preserves_pointwise_values
set_option pp.all true in
#check @complete_source_pack_walk_has_exact_ordered_chunk_integer_field_values
#print axioms complete_source_pack_walk_has_exact_ordered_chunk_integer_field_values
set_option pp.all true in
#check @complete_source31_byte_chunk_walk_preserves_exact_input_order
#print axioms complete_source31_byte_chunk_walk_preserves_exact_input_order
set_option pp.all true in
#check @complete_source_byte_packing_is_injective_when_exact_input_length_is_bound
#print axioms complete_source_byte_packing_is_injective_when_exact_input_length_is_bound
end ShielddSecurity.TransferScalarPackWalk01
