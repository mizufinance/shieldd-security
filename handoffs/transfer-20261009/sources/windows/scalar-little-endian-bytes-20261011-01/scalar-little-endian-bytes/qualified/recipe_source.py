"""Symbolic typed-byte serialization of the finite four-limb carry/sub/add-back result."""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
domain=json.loads((DIAG/'transfer-bounded-native-codec-20261011-02/context/canonical-domain.json').read_bytes())
row=next(r for r in domain['library_sources'] if r['path'].endswith('-scalar.rs'))
scalar=Path(row['path']); data=scalar.read_bytes(); assert hashlib.sha256(data).hexdigest()==row['sha256']
text=data.decode()
assert re.search(r'pub struct Scalar\(pub\(crate\) \[u64; 4\]\);',text)
byteLines=[]
for i in range(4):
    line=f'res[{i*8}..{(i+1)*8}].copy_from_slice(&tmp.0[{i}].to_le_bytes());'
    assert text.count(line)==1
    byteLines.append(line)
(ROOT/'context').mkdir()
(ROOT/'context/serializer-byte-shape.json').write_text(json.dumps({'scalar_source':row,'scalar_internal_array':'[u64;4]','byte_slices':byteLines,'bytes':32,'scope':'Exact pinned type/byte-slice/order source shape only. Typed UInt8 recursive LE representation is an arithmetic model; Rust primitive to_le_bytes/memory/vector/native trace correspondence remains separate.'},indent=2,sort_keys=True)+'\n')
source='''import ShielddSecurity.TransferScalarMaskedNormalization01
import Init.Data.Vector.Lemmas
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarLittleEndianBytes01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarFourRoundWrapper01 (nativeRounds)
open TransferScalarMaskedNormalization01 (sourceNormalize)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Symbolic typed UInt8 little-endian codec and exact four-limb source-shaped
serialization. Finite UInt64 inputs supply word bounds; byte width/order,
numeric reconstruction and canonical field range are derived from the actual
carry/sub/add-back model. No byte-range or canonical-input bound is supplied.
Pinned Rust array/slice order is checked separately from to_le_bytes, native
trace, Scalar Montgomery semantic identity and typed runtime projection. -/
def encodeLE : Nat → Nat → List UInt8
  | 0, _ => []
  | width + 1, value => UInt8.ofNat (value % 256) :: encodeLE width (value / 256)
def decodeLE : List UInt8 → Nat
  | [] => 0
  | byte :: rest => byte.toNat + 256 * decodeLE rest
def wordBytes (word : UInt64) : List UInt8 := encodeLE 8 word.toNat
def wordsBytes : List UInt64 → List UInt8
  | [] => []
  | word :: rest => wordBytes word ++ wordsBytes rest
def serializerBytes (words : List UInt64) : List UInt8 := wordsBytes (sourceNormalize (nativeRounds 4 words))
def scalarKey (words : Vector UInt64 4) : Nat := decodeLE (serializerBytes words.toList)

theorem typed_little_endian_encoding_has_exact_width (width value : Nat) :
    (encodeLE width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih =>
    change (encodeLE width (value / 256)).length + 1 = width + 1
    rw [ih]

theorem little_endian_append_preserves_positional_value (left right : List UInt8) :
    decodeLE (left ++ right) = decodeLE left + 256 ^ left.length * decodeLE right := by
  induction left with
  | nil => simp only [List.nil_append, decodeLE, List.length_nil, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
  | cons byte rest ih =>
    change byte.toNat + 256 * decodeLE (rest ++ right) =
      (byte.toNat + 256 * decodeLE rest) + 256 ^ (rest.length + 1) * decodeLE right
    rw [ih, Nat.pow_succ, Nat.mul_add]
    ac_rfl

theorem typed_little_endian_encoding_reconstructs_bounded_integer
    (width value : Nat) (bounded : value < 256 ^ width) : decodeLE (encodeLE width value) = value := by
  induction width generalizing value with
  | zero =>
    have zero : value = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ bounded)
    subst value
    rfl
  | succ width ih =>
    have quotient : value / 256 < 256 ^ width :=
      (Nat.div_lt_iff_lt_mul (by decide)).2 (by simpa only [Nat.pow_succ] using bounded)
    have remainder : value % 256 < 256 := Nat.mod_lt _ (by decide)
    change (value % 256) % 256 + 256 * decodeLE (encodeLE width (value / 256)) = value
    rw [Nat.mod_eq_of_lt remainder, ih _ quotient]
    exact Nat.mod_add_div value 256

theorem word_bytes_reconstruct_actual_finite_u64 (word : UInt64) : decodeLE (wordBytes word) = word.toNat := by
  exact typed_little_endian_encoding_reconstructs_bounded_integer 8 word.toNat word.toNat_lt

theorem serialized_word_vector_has_eight_bytes_per_word (words : List UInt64) :
    (wordsBytes words).length = 8 * words.length := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
    change (wordBytes word ++ wordsBytes rest).length = 8 * (rest.length + 1)
    rw [List.length_append, wordBytes, typed_little_endian_encoding_has_exact_width, ih, Nat.mul_add, Nat.mul_one]
    ac_rfl

theorem serialized_word_vector_reconstructs_actual_packed_words (words : List UInt64) :
    decodeLE (wordsBytes words) = packWords words := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
    change decodeLE (wordBytes word ++ wordsBytes rest) = word.toNat + radix64 * packWords rest
    rw [little_endian_append_preserves_positional_value, word_bytes_reconstruct_actual_finite_u64,
      wordBytes, typed_little_endian_encoding_has_exact_width, ih]
    rfl

theorem source_scalar_serialization_has_exact_32_byte_width (words : List UInt64) (four : words.length = 4) :
    (serializerBytes words).length = 32 := by
  unfold serializerBytes
  rw [serialized_word_vector_has_eight_bytes_per_word,
    TransferScalarMaskedNormalization01.source_normalization_retains_four_word_width _
      (TransferScalarFourRoundWrapper01.native_round_walk_preserves_four_word_width 4 words four)]

theorem source_scalar_serialization_reconstructs_canonical_field_value (words : List UInt64) (four : words.length = 4) :
    decodeLE (serializerBytes words) < nullifierModulus := by
  unfold serializerBytes
  rw [serialized_word_vector_reconstructs_actual_packed_words]
  exact TransferScalarMaskedNormalization01.four_round_source_sub_and_addback_have_canonical_field_range words four

theorem fixed_four_word_source_scalar_projection_is_canonical (words : Vector UInt64 4) : scalarKey words < nullifierModulus := by
  exact source_scalar_serialization_reconstructs_canonical_field_value words.toList Vector.length_toList

'''
names=['encodeLE','decodeLE','wordBytes','wordsBytes','serializerBytes','scalarKey','typed_little_endian_encoding_has_exact_width','little_endian_append_preserves_positional_value','typed_little_endian_encoding_reconstructs_bounded_integer','word_bytes_reconstruct_actual_finite_u64','serialized_word_vector_has_eight_bytes_per_word','serialized_word_vector_reconstructs_actual_packed_words','source_scalar_serialization_has_exact_32_byte_width','source_scalar_serialization_reconstructs_canonical_field_value','fixed_four_word_source_scalar_projection_is_canonical']
for name in names:
    source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferScalarLittleEndianBytes01\n'
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferScalarLittleEndianBytes01.lean').write_text(source)
s=(DIAG/'transfer-scalar-masked-normalization-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-scalar-borrow-walk-20261011-01'", "UPSTREAM = DIAG / 'transfer-scalar-masked-normalization-20261011-02'")
replace("POOL = DIAG / 'transfer-scalar-masked-normalization-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-scalar-little-endian-bytes-owned-floor-20261011-02'")
replace("MODULE = 'TransferScalarMaskedNormalization01'", "MODULE = 'TransferScalarLittleEndianBytes01'")
s=s.replace("'runs/01-TransferScalarBorrowWalk01/stdout.txt'", "'runs/01-TransferScalarMaskedNormalization01/stdout.txt'",1)
replace('assert len(current) == 7','assert len(current) == 10')
replace("records.append(('TransferScalarBorrowWalk01'", "records.append(('TransferScalarMaskedNormalization01'")
replace("    'handwritten/TransferScalarBorrowWalk01.lean', 'project/ShielddSecurity/TransferScalarBorrowWalk01.lean']]", "    'handwritten/TransferScalarMaskedNormalization01.lean', 'project/ShielddSecurity/TransferScalarMaskedNormalization01.lean']]")
replace('assert len(records) == 85 and len(audits) == 801','assert len(records) == 86 and len(audits) == 811')
replace("'objects': 85", "'objects': 86")
s=s.replace('eighty-five-module','eighty-six-module').replace('801 inherited','811 inherited')
replace("'imports': ['ShielddSecurity.TransferScalarBorrowWalk01','Init.Data.UInt.Bitwise']", "'imports': ['ShielddSecurity.TransferScalarMaskedNormalization01','Init.Data.Vector.Lemmas']")
replace('assert len(names) == 10','assert len(names) == 15')
replace("'fresh_audits': 10", "'fresh_audits': 15")
replace("[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', runner")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Typed UInt8 symbolic little-endian width and numeric reconstruction; finite UInt64 word chunks reconstruct actual packed source normalization words. Exact four-word serializer derives 32 bytes and numeric value below nullifier modulus from actual finite carry/sub/AND/add-back model, with no byte validity/canonical input range supplied. Fixed Vector UInt64 4 projection has canonical field range. Fifteen full reports: six definitions/nine theorems. Pinned Scalar internal [u64;4] and ordered four 8-byte little-endian output slices statically checked; actual Rust to_le_bytes/native trace/Scalar Montgomery semantic identity and runtime typed input projection remain interfaces. Zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
anchor="mapping['serializer_wrapper_source_association'] = "
start=s.index(anchor);end=s.index('\n',start)
s=s[:end]+"\nmapping['serializer_byte_source_association'] = pin(ROOT/'context/serializer-byte-shape.json')"+s[end:]
s=s.replace("plan['pins'] += wordContext + [mapping['serializer_wrapper_source_association']]", "plan['pins'] += wordContext + [mapping['serializer_wrapper_source_association'], mapping['serializer_byte_source_association']]",1)
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh typed little-endian 32-byte serializer range/projection refinement on exact 811-report/86-module qualified ancestry. Symbolic width/vector recurrences, no prior replay; preserved source/diagnostic identities and all guards unchanged.'"+s[end:]
s=s.replace('SOURCE_SCALAR_MASKED_SUBTRACTION_ADD_BACK_EXACT_NORMALIZATION','SOURCE_SCALAR_TYPED_LITTLE_ENDIAN_32_BYTE_CANONICAL_PROJECTION')
s=s.replace('SCALAR_MASKED_NORMALIZATION_COMPLETE_EIGHTY_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SCALAR_LITTLE_ENDIAN_BYTES_COMPLETE_EIGHTY_SIX_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'inherited_audits': 801", "'inherited_audits': 811")

retained = "failedBytes = DIAG/'transfer-scalar-little-endian-bytes-20261011-01'\nplan['pins'] += [pin(failedBytes/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/serializer-byte-shape.json','handwritten/TransferScalarLittleEndianBytes01.lean','project/ShielddSecurity/TransferScalarLittleEndianBytes01.lean','runs/01-TransferScalarLittleEndianBytes01/stdout.txt']]\n"
s=s.replace('unique = {}', retained+'unique = {}',1)
s=s.replace("[Path(__file__), ROOT / 'prepare_recipe.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner",1)
s=s.replace('Fresh typed little-endian 32-byte serializer range/projection refinement', 'Fresh02 proof-only wordBytes wrapper unfolding at two exact-width rewrites; all fifteen declarations unchanged, failed01 full raw diagnostics retained with zero credit. Fresh typed little-endian 32-byte serializer range/projection refinement')

(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':15,'inherited_reports':811,'owned_modules':86,'native_correspondence_still_open':True})
