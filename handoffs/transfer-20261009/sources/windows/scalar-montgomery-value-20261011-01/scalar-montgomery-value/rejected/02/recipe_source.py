"""Symbolic modular semantics for actual source-shaped four-round scalar serializer."""
import re
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
p=52435875175126190479447740508185965837690552500527637822603658699938581184513
rho=pow(2**256,-1,p)
assert (rho*2**256)%p==1
source='''import ShielddSecurity.TransferScalarLittleEndianBytes01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarMontgomeryValue01
open TransferScalarSerializationRange01 (radix64 normalize)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarFourRoundWrapper01 (modulusWords inverseWord nativeRound nativeRounds)
open TransferScalarMaskedNormalization01 (sourceNormalize)
open TransferScalarLittleEndianBytes01 (decodeLE serializerBytes scalarKey)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Exact modular value of the finite source-shaped Montgomery serializer.
Source INV cancellation is proved as a closed integer certificate, then lifted
to all finite UInt64 low words. Small reusable lemmas and a symbolic round
induction derive the radix-power relation. Normalization and typed LE encoding
retain that relation; a kernel-checked constant radix inverse gives the exact
canonical mathematical projection. Rust primitive/trace/type interpretation
correspondence remains separate. No caller-provided cancellation or desired
output premise, no primality or curve replay, no wide unrolled constraints. -/

def radixInverse : Nat := RHO_LITERAL

def montgomeryValue (words : Vector UInt64 4) : Nat :=
  radixInverse * packWords words.toList % nullifierModulus

theorem source_inverse_word_cancels_modulus_low_word :
    (1 + inverseWord.toNat * (modulusWords.headD 0).toNat) % radix64 = 0 := by decide

theorem packed_vector_modulo_radix_is_actual_low_word (words : List UInt64) :
    packWords words % radix64 = (words.headD 0).toNat := by
  cases words with
  | nil => rfl
  | cons word rest =>
    change (word.toNat + radix64 * packWords rest) % radix64 = word.toNat
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt word.toNat_lt

theorem source_modulus_modulo_radix_is_actual_low_word :
    nullifierModulus % radix64 = (modulusWords.headD 0).toNat := by
  rw [← TransferScalarFourRoundWrapper01.modulus_words_pack_to_actual_nullifier_modulus]
  exact packed_vector_modulo_radix_is_actual_low_word modulusWords

theorem wrapped_source_multiplier_cancels_any_low_word (word : UInt64) :
    (word.toNat + (word * inverseWord).toNat * (modulusWords.headD 0).toNat) % radix64 = 0 := by
  rw [UInt64.toNat_mul]
  change (word.toNat + (word.toNat * inverseWord.toNat % radix64) * (modulusWords.headD 0).toNat) % radix64 = 0
  rw [Nat.add_mod, Nat.mod_mul_mod, Nat.mod_eq_of_lt word.toNat_lt, Nat.add_mod_mod]
  have factored : word.toNat + word.toNat * inverseWord.toNat * (modulusWords.headD 0).toNat =
      word.toNat * (1 + inverseWord.toNat * (modulusWords.headD 0).toNat) := by
    rw [Nat.mul_add, Nat.mul_one]
    ac_rfl
  rw [factored, Nat.mul_mod, source_inverse_word_cancels_modulus_low_word, Nat.mul_zero, Nat.zero_mod]

theorem derived_round_numerator_is_divisible_by_radix (words : List UInt64) :
    (packWords words + (words.headD 0 * inverseWord).toNat * nullifierModulus) % radix64 = 0 := by
  have finite : (words.headD 0 * inverseWord).toNat < radix64 := (words.headD 0 * inverseWord).toNat_lt
  rw [Nat.add_mod, Nat.mul_mod, packed_vector_modulo_radix_is_actual_low_word,
    source_modulus_modulo_radix_is_actual_low_word, Nat.mod_eq_of_lt finite, Nat.add_mod_mod]
  exact wrapped_source_multiplier_cancels_any_low_word (words.headD 0)

theorem native_round_has_exact_montgomery_integer_equation (words : List UInt64) (four : words.length = 4) :
    radix64 * packWords (nativeRound words) =
      packWords words + (words.headD 0 * inverseWord).toNat * nullifierModulus := by
  rw [TransferScalarFourRoundWrapper01.one_native_round_packs_to_derived_radix_quotient words four]
  have exactDivision := Nat.mod_add_div
    (packWords words + (words.headD 0 * inverseWord).toNat * nullifierModulus) radix64
  rw [derived_round_numerator_is_divisible_by_radix, Nat.zero_add] at exactDivision
  exact exactDivision

theorem symbolic_native_round_walk_preserves_montgomery_modular_value
    (rounds : Nat) (words : List UInt64) (four : words.length = 4) :
    (radix64 ^ rounds * packWords (nativeRounds rounds words)) % nullifierModulus =
      packWords words % nullifierModulus := by
  induction rounds generalizing words with
  | zero => simp only [Nat.pow_zero, nativeRounds, Nat.one_mul]
  | succ rounds ih =>
    change (radix64 ^ (rounds + 1) * packWords (nativeRounds rounds (nativeRound words))) % nullifierModulus = _
    have reassoc : radix64 ^ (rounds + 1) * packWords (nativeRounds rounds (nativeRound words)) =
        radix64 * (radix64 ^ rounds * packWords (nativeRounds rounds (nativeRound words))) := by
      rw [Nat.pow_succ]
      ac_rfl
    rw [reassoc, Nat.mul_mod, ih (nativeRound words)
      (TransferScalarFourRoundWrapper01.one_native_round_preserves_four_word_width words four),
      ← Nat.mul_mod, native_round_has_exact_montgomery_integer_equation words four,
      Nat.add_mul_mod_self_right]

theorem single_modulus_normalization_preserves_modular_value (value : Nat) :
    normalize nullifierModulus value % nullifierModulus = value % nullifierModulus := by
  by_cases enough : nullifierModulus ≤ value
  · rw [normalize, if_pos enough]
    have restored := congrArg (fun v => v % nullifierModulus) (Nat.sub_add_cancel enough)
    change (value - nullifierModulus + nullifierModulus) % nullifierModulus = value % nullifierModulus at restored
    rw [Nat.add_mod_right] at restored
    exact restored
  · rw [normalize, if_neg enough]

theorem typed_source_serializer_preserves_four_round_montgomery_relation
    (words : List UInt64) (four : words.length = 4) :
    (radix64 ^ 4 * decodeLE (serializerBytes words)) % nullifierModulus =
      packWords words % nullifierModulus := by
  unfold serializerBytes
  rw [TransferScalarLittleEndianBytes01.serialized_word_vector_reconstructs_actual_packed_words,
    TransferScalarMaskedNormalization01.source_sub_and_masked_addback_equal_single_modulus_normalization _
      (TransferScalarFourRoundWrapper01.native_round_walk_preserves_four_word_width 4 words four),
    Nat.mul_mod, single_modulus_normalization_preserves_modular_value, ← Nat.mul_mod]
  exact symbolic_native_round_walk_preserves_montgomery_modular_value 4 words four

theorem source_four_word_radix_inverse_is_exact :
    (radixInverse * radix64 ^ 4) % nullifierModulus = 1 := by decide

theorem fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value (words : Vector UInt64 4) :
    scalarKey words = montgomeryValue words := by
  have relation := typed_source_serializer_preserves_four_round_montgomery_relation words.toList Vector.length_toList
  change (radix64 ^ 4 * scalarKey words) % nullifierModulus = packWords words.toList % nullifierModulus at relation
  have scaled := congrArg (fun value => radixInverse * value % nullifierModulus) relation
  simp only [Nat.mul_mod_mod] at scaled
  rw [← Nat.mul_assoc, Nat.mul_mod, source_four_word_radix_inverse_is_exact,
    Nat.one_mul, Nat.mod_mod,
    Nat.mod_eq_of_lt (TransferScalarLittleEndianBytes01.fixed_four_word_source_scalar_projection_is_canonical words)] at scaled
  exact scaled

'''.replace('RHO_LITERAL',str(rho))
names=re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',source,re.M)
assert len(names)==13
for name in names:
    source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferScalarMontgomeryValue01\n'
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferScalarMontgomeryValue01.lean').write_text(source)
s=(DIAG/'transfer-scalar-little-endian-bytes-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-scalar-masked-normalization-20261011-02'", "UPSTREAM = DIAG / 'transfer-scalar-little-endian-bytes-20261011-02'")
replace("POOL = DIAG / 'transfer-scalar-little-endian-bytes-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-scalar-montgomery-value-owned-floor-20261011-02'")
replace("MODULE = 'TransferScalarLittleEndianBytes01'", "MODULE = 'TransferScalarMontgomeryValue01'")
s=s.replace("'runs/01-TransferScalarMaskedNormalization01/stdout.txt'", "'runs/01-TransferScalarLittleEndianBytes01/stdout.txt'",1)
replace('assert len(current) == 10','assert len(current) == 15')
replace("records.append(('TransferScalarMaskedNormalization01'", "records.append(('TransferScalarLittleEndianBytes01'")
replace("    'handwritten/TransferScalarMaskedNormalization01.lean', 'project/ShielddSecurity/TransferScalarMaskedNormalization01.lean']]", "    'handwritten/TransferScalarLittleEndianBytes01.lean', 'project/ShielddSecurity/TransferScalarLittleEndianBytes01.lean']]")
replace('assert len(records) == 86 and len(audits) == 811','assert len(records) == 87 and len(audits) == 826')
replace("'objects': 86", "'objects': 87")
s=s.replace('eighty-six-module','eighty-seven-module').replace('811 inherited','826 inherited')
replace("'imports': ['ShielddSecurity.TransferScalarMaskedNormalization01','Init.Data.Vector.Lemmas']", "'imports': ['ShielddSecurity.TransferScalarLittleEndianBytes01']")
replace('assert len(names) == 15','assert len(names) == 13')
replace("'fresh_audits': 15", "'fresh_audits': 13")
replace("[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', runner")
replace("pin(ROOT/'context/serializer-byte-shape.json')", "pin(DIAG/'transfer-scalar-little-endian-bytes-20261011-02/context/serializer-byte-shape.json')")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Source-shaped finite Montgomery serializer has exact canonical mathematical value, derived from source INV cancellation, actual wrapped low-word multiplier, exact divisible-round equation, symbolic arbitrary round induction, masked normalization and typed LE bytes. Fixed Vector UInt64 4 projection equals kernel-checked radix inverse times raw packed words modulo actual nullifier modulus. Thirteen full reports: two definitions/eleven theorems. No caller-supplied cancellation, desired output or canonical raw range; no primality/curve replay. Actual Rust primitive/native trace/Scalar Montgomery interpretation/runtime typed projection remain separate correspondence obligations. Zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh symbolic Montgomery value refinement on exact 826-report/87-module qualified ancestry. Closed INV/radix inverse certificates and small reusable modular lemmas, no prior replay; preserved source/diagnostic identities and all guards unchanged.'"+s[end:]
s=s.replace('SOURCE_SCALAR_TYPED_LITTLE_ENDIAN_32_BYTE_CANONICAL_PROJECTION','SOURCE_SCALAR_EXACT_CANONICAL_MONTGOMERY_VALUE')
s=s.replace('SCALAR_LITTLE_ENDIAN_BYTES_COMPLETE_EIGHTY_SIX_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SCALAR_MONTGOMERY_VALUE_COMPLETE_EIGHTY_SEVEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'inherited_audits': 811", "'inherited_audits': 826")

retained = "failedMontgomery = DIAG/'transfer-scalar-montgomery-value-20261011-01'\nplan['pins'] += [pin(failedMontgomery/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarMontgomeryValue01.lean','project/ShielddSecurity/TransferScalarMontgomeryValue01.lean','runs/01-TransferScalarMontgomeryValue01/stdout.txt']]\n"
s=s.replace('unique = {}',retained+'unique = {}',1)
s=s.replace("[Path(__file__), ROOT / 'prepare_recipe.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner",1)
s=s.replace('Fresh symbolic Montgomery value refinement', 'Fresh02 proof-only nonlooping modular rewrites and explicit congrArg reduction, all thirteen contracts unchanged; failed01 warning/errors/full raw reports retained with zero credit. Fresh symbolic Montgomery value refinement')

(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':13,'inherited_reports':826,'owned_modules':87,'native_correspondence_still_open':True})
