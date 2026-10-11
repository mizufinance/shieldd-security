"""Link canonical internal scalar word equality, mathematical value and exact bytes."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
source='''import ShielddSecurity.TransferCompleteBlockDriver01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCanonicalWordEquality01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarLittleEndianBytes01 (scalarKey serializerBytes)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Symbolic equal-width u64 packing injection and canonical internal-word
Montgomery bijection. Under explicit canonical internal raw representation,
raw vector equality iff mathematical scalar equality iff exact source bytes.
Canonical domain excludes raw aliases modulo p; arbitrary raw vectors are
not claimed to have injective scalar serialization. Native private Scalar
representation invariant/PartialEq/constant-time primitives/word selector/
byte/hash/Clone/collection correspondence remains explicit; no native credit. -/

structure CanonicalScalar where
  words : Vector UInt64 4
  canonical : packWords words.toList < nullifierModulus

theorem packed_word_cons_division_recovers_exact_tail (word : UInt64) (rest : List UInt64) :
    packWords (word :: rest) / radix64 = packWords rest := by
  have bounded : word.toNat < radix64 := word.toNat_lt
  change (word.toNat + radix64 * packWords rest) / radix64 = packWords rest
  rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt bounded, Nat.zero_add]

theorem equal_width_packed_u64_lists_are_equal (left right : List UInt64)
    (width : left.length = right.length) (packed : packWords left = packWords right) : left = right := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons head rest => simp only [List.length_nil, List.length_cons] at width; omega
  | cons head rest ih =>
    cases right with
    | nil => simp only [List.length_nil, List.length_cons] at width; omega
    | cons other tail =>
      have lengths : rest.length = tail.length := Nat.succ.inj width
      have heads := congrArg (fun value => value % radix64) packed
      simp only [TransferScalarMontgomeryValue01.packed_vector_modulo_radix_is_actual_low_word, List.headD_cons] at heads
      have headEq : head = other := UInt64.toNat_inj.mp heads
      have tails := congrArg (fun value => value / radix64) packed
      rw [packed_word_cons_division_recovers_exact_tail, packed_word_cons_division_recovers_exact_tail] at tails
      exact (congrArg (fun word : UInt64 => word :: rest) headEq).trans (congrArg (List.cons other) (ih tail lengths tails))

theorem packed_fixed_word_vectors_equal_iff_raw_vectors_equal (left right : Vector UInt64 4) :
    packWords left.toList = packWords right.toList ↔ left = right := by
  constructor
  · intro same
    exact Vector.toList_inj.mp (equal_width_packed_u64_lists_are_equal left.toList right.toList (by simp only [Vector.length_toList]) same)
  · intro same
    exact congrArg (fun words : Vector UInt64 4 => packWords words.toList) same

theorem canonical_internal_math_values_equal_iff_raw_words_equal (left right : CanonicalScalar) :
    montgomeryValue left.words = montgomeryValue right.words ↔ left.words = right.words := by
  constructor
  · intro same
    have leftRelation := TransferScalarMontgomeryValue01.typed_source_serializer_preserves_four_round_montgomery_relation left.words.toList Vector.length_toList
    have rightRelation := TransferScalarMontgomeryValue01.typed_source_serializer_preserves_four_round_montgomery_relation right.words.toList Vector.length_toList
    change (radix64 ^ 4 * scalarKey left.words) % nullifierModulus = packWords left.words.toList % nullifierModulus at leftRelation
    change (radix64 ^ 4 * scalarKey right.words) % nullifierModulus = packWords right.words.toList % nullifierModulus at rightRelation
    rw [TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value] at leftRelation rightRelation
    have packed := congrArg (fun value => radix64 ^ 4 * value % nullifierModulus) same
    rw [leftRelation, rightRelation, Nat.mod_eq_of_lt left.canonical, Nat.mod_eq_of_lt right.canonical] at packed
    exact (packed_fixed_word_vectors_equal_iff_raw_vectors_equal left.words right.words).mp packed
  · intro same
    exact congrArg montgomeryValue same

theorem canonical_internal_source_bytes_equal_iff_raw_words_equal (left right : CanonicalScalar) :
    serializerBytes left.words.toList = serializerBytes right.words.toList ↔ left.words = right.words :=
  (TransferScalarByteEquality01.source_scalar_typed_byte_keys_equal_iff_mathematical_montgomery_values_equal left.words right.words).trans
    (canonical_internal_math_values_equal_iff_raw_words_equal left right)

'''
names=re.findall(r'^(?:structure|theorem) ([A-Za-z0-9_]+)',source,re.M);assert len(names)==6
for name in names:source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferCanonicalWordEquality01\n'
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferCanonicalWordEquality01.lean').write_text(source)
s=(DIAG/'transfer-complete-block-driver-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-absent-start-publication-20261011-01'", "UPSTREAM = DIAG / 'transfer-complete-block-driver-20261011-02'")
replace("POOL = DIAG / 'transfer-complete-block-driver-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-canonical-word-equality-owned-floor-20261011-01'")
replace("MODULE = 'TransferCompleteBlockDriver01'", "MODULE = 'TransferCanonicalWordEquality01'")
replace("stdout = UPSTREAM / 'runs/01-TransferAbsentStartPublication01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferCompleteBlockDriver01/stdout.txt'")
replace('assert len(current) == 4','assert len(current) == 2')
replace("records.append(('TransferAbsentStartPublication01'", "records.append(('TransferCompleteBlockDriver01'")
replace("    'handwritten/TransferAbsentStartPublication01.lean', 'project/ShielddSecurity/TransferAbsentStartPublication01.lean']]", "    'handwritten/TransferCompleteBlockDriver01.lean', 'project/ShielddSecurity/TransferCompleteBlockDriver01.lean']]")
replace('assert len(records) == 100 and len(audits) == 909','assert len(records) == 101 and len(audits) == 911')
replace("'objects': 100", "'objects': 101")
s=s.replace('one-hundred-module','one-hundred-one-module').replace('909 inherited','911 inherited')
replace("'imports': ['ShielddSecurity.TransferAbsentStartPublication01']", "'imports': ['ShielddSecurity.TransferCompleteBlockDriver01']")
replace('assert len(names) == 2','assert len(names) == 6');replace("'fresh_audits': 2", "'fresh_audits': 6")
replace("[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', runner")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Symbolic equal-width u64 packing is injective; finite four-word vector packing equality is exactly raw vector equality. Canonical internal raw Scalar domain then proves mathematical Montgomery value equality iff raw word equality iff exact source serializer bytes equality. Six complete reports: one structure/five theorems. Canonical representation is an explicit typed domain, not inferred for arbitrary raw words; modulo aliases outside it are excluded. Native private Scalar invariant/PartialEq/constant-time primitive/word selector/byte/hash/Clone/collection/full trace binding remains explicit. Zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
s=s.replace('COMPLETE_BLOCK_DRIVER_COMPLETE_ONE_HUNDRED_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','CANONICAL_WORD_EQUALITY_COMPLETE_ONE_HUNDRED_ONE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN').replace("'inherited_audits': 909", "'inherited_audits': 911")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':6,'inherited_reports':911,'owned_modules':101,'full_native_trace_still_open':True})
