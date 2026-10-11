"""Connect finite u64 inputs and widened word arithmetic to the scalar range recurrence."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
source='''import ShielddSecurity.TransferScalarSerializationRange01
import Init.Data.BitVec.Lemmas
import Init.Data.UInt.Lemmas
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarWordPrimitives01
open TransferScalarSerializationRange01 (radix64 reduceRounds normalize)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Exact finite-word arithmetic model for the pinned scalar util.rs operations.
u64 packing supplies the raw range premise; a widened 128-bit MAC is proved
nonoverflowing and its low/high u64 split conserves the full integer value.
These Lean UInt64/BitVec semantics still require correspondence to Rust
primitive evaluation and the actual four-round carry schedule and sub/byte
layout. Registry source identity is not semantic proof or runtime testing. -/
def packWords : List UInt64 → Nat
  | [] => 0
  | word :: rest => word.toNat + radix64 * packWords rest

def mac128 (a b c carry : UInt64) : BitVec 128 :=
  BitVec.ofNat 128 a.toNat + BitVec.ofNat 128 b.toNat * BitVec.ofNat 128 c.toNat + BitVec.ofNat 128 carry.toNat

def split128 (ret : BitVec 128) : UInt64 × UInt64 :=
  (UInt64.ofNat ret.toNat, UInt64.ofNat (ret.toNat / radix64))

def scalarReduction (raw multipliers : List UInt64) : Nat :=
  normalize nullifierModulus (reduceRounds nullifierModulus radix64 (packWords raw) (multipliers.map UInt64.toNat))

theorem packed_u64_vector_is_below_radix_power (words : List UInt64) :
    packWords words < radix64 ^ words.length := by
  induction words with
  | nil => decide
  | cons word rest ih =>
    change word.toNat + radix64 * packWords rest < radix64 ^ (rest.length + 1)
    calc
      word.toNat + radix64 * packWords rest < radix64 + radix64 * packWords rest :=
        Nat.add_lt_add_right word.toNat_lt _
      _ = radix64 * (packWords rest + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ radix64 * radix64 ^ rest.length := Nat.mul_le_mul_left radix64 (Nat.succ_le_of_lt ih)
      _ = radix64 ^ (rest.length + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

theorem multiply_accumulate_of_four_words_fits_double_width
    (radix a b c carry : Nat) (positive : 0 < radix)
    (ha : a < radix) (hb : b < radix) (hc : c < radix) (hd : carry < radix) :
    a + b * c + carry < radix * radix := by
  have upper : a + b * c + carry ≤ (radix - 1) + (radix - 1) * (radix - 1) + (radix - 1) :=
    Nat.add_le_add (Nat.add_le_add (Nat.le_sub_one_of_lt ha)
      (Nat.mul_le_mul (Nat.le_sub_one_of_lt hb) (Nat.le_sub_one_of_lt hc))) (Nat.le_sub_one_of_lt hd)
  have square : (radix - 1) + (radix - 1) * (radix - 1) + (radix - 1) + 1 = radix * radix := by
    calc
      _ = ((radix - 1) + 1) * ((radix - 1) + 1) := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      _ = radix * radix := by rw [Nat.sub_add_cancel positive]
  exact Nat.lt_of_le_of_lt upper (Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) square)

theorem widened_u64_mac_preserves_full_integer (a b c carry : UInt64) :
    (mac128 a b c carry).toNat = a.toNat + b.toNat * c.toNat + carry.toNat := by
  have bounded := multiply_accumulate_of_four_words_fits_double_width radix64
    a.toNat b.toNat c.toNat carry.toNat (by decide) a.toNat_lt b.toNat_lt c.toNat_lt carry.toNat_lt
  change (((a.toNat % 2 ^ 128 + (b.toNat % 2 ^ 128 * (c.toNat % 2 ^ 128)) % 2 ^ 128) % 2 ^ 128) + carry.toNat % 2 ^ 128) % 2 ^ 128 = _
  rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mod_add_mod, Nat.add_mod_mod]
  exact Nat.mod_eq_of_lt bounded

theorem split_double_word_preserves_full_integer (ret : BitVec 128) :
    (split128 ret).1.toNat + radix64 * (split128 ret).2.toNat = ret.toNat := by
  have bounded : ret.toNat < radix64 * radix64 := ret.isLt
  have carryBound : ret.toNat / radix64 < radix64 := (Nat.div_lt_iff_lt_mul (by decide)).2 bounded
  change ret.toNat % 2 ^ 64 + radix64 * ((ret.toNat / radix64) % 2 ^ 64) = ret.toNat
  rw [Nat.mod_eq_of_lt carryBound]
  exact Nat.mod_add_div ret.toNat radix64

theorem widened_u64_mac_low_word_and_carry_conserve_value (a b c carry : UInt64) :
    (split128 (mac128 a b c carry)).1.toNat + radix64 * (split128 (mac128 a b c carry)).2.toNat =
      a.toNat + b.toNat * c.toNat + carry.toNat := by
  rw [split_double_word_preserves_full_integer, widened_u64_mac_preserves_full_integer]

theorem four_actual_u64_inputs_and_multipliers_reduce_into_canonical_field
    (raw multipliers : List UInt64) (fourRaw : raw.length = 4) (fourMultipliers : multipliers.length = 4) :
    scalarReduction raw multipliers < nullifierModulus := by
  apply TransferScalarSerializationRange01.final_subtraction_is_canonical nullifierModulus _ (by decide)
  apply TransferScalarSerializationRange01.all_rounds_finish_at_most_modulus nullifierModulus radix64
    (multipliers.map UInt64.toNat) (by decide)
  · intro digit inside
    obtain ⟨word, _, value⟩ := List.mem_map.mp inside
    subst digit
    exact word.toNat_lt
  · have bounded := packed_u64_vector_is_below_radix_power raw
    rw [List.length_map, fourMultipliers]
    rw [fourRaw] at bounded
    exact Nat.lt_of_lt_of_le bounded (Nat.le_add_left _ _)

'''
names=['packWords','mac128','split128','scalarReduction','packed_u64_vector_is_below_radix_power','multiply_accumulate_of_four_words_fits_double_width','widened_u64_mac_preserves_full_integer','split_double_word_preserves_full_integer','widened_u64_mac_low_word_and_carry_conserve_value','four_actual_u64_inputs_and_multipliers_reduce_into_canonical_field']
for name in names:
    source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferScalarWordPrimitives01\n'
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferScalarWordPrimitives01.lean').write_text(source)
s=(DIAG/'transfer-scalar-serialization-range-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-native-only-publication-20261011-01'", "UPSTREAM = DIAG / 'transfer-scalar-serialization-range-20261011-02'")
replace("POOL = DIAG / 'transfer-scalar-serialization-range-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-scalar-word-primitives-owned-floor-20261011-02'")
replace("MODULE = 'TransferScalarSerializationRange01'", "MODULE = 'TransferScalarWordPrimitives01'")
s=s.replace("'runs/01-TransferNativeOnlyPublication01/stdout.txt'", "'runs/01-TransferScalarSerializationRange01/stdout.txt'",1)
replace('assert len(current) == 1','assert len(current) == 8')
replace("records.append(('TransferNativeOnlyPublication01'", "records.append(('TransferScalarSerializationRange01'")
replace("    'handwritten/TransferNativeOnlyPublication01.lean', 'project/ShielddSecurity/TransferNativeOnlyPublication01.lean']]", "    'handwritten/TransferScalarSerializationRange01.lean', 'project/ShielddSecurity/TransferScalarSerializationRange01.lean']]")
replace('assert len(records) == 78 and len(audits) == 738','assert len(records) == 79 and len(audits) == 746')
replace("'objects': 78", "'objects': 79")
s=s.replace('seventy-eight-module','seventy-nine-module').replace('738 inherited','746 inherited')
replace("'imports': ['ShielddSecurity.TransferNativeOnlyPublication01']", "'imports': ['ShielddSecurity.TransferScalarSerializationRange01','Init.Data.BitVec.Lemmas','Init.Data.UInt.Lemmas']")
replace('assert len(names) == 8','assert len(names) == 10')
replace("'fresh_audits': 8", "'fresh_audits': 10")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Finite UInt64 little-endian limb packing derives the raw four-word bound instead of assuming it. Widened BitVec128 multiply-accumulate of four UInt64 inputs never overflows; low UInt64/carry split conserves the exact full integer. Four arbitrary actual finite UInt64 inputs and four finite UInt64 multipliers reduce below the exact nullifier field modulus. Ten full reports: four definitions and six theorems. Pinned util.rs MAC/ADC/SBB source copied read-only with raw source identity and optional cached archive authentication against exact Cargo.lock; Rust primitive evaluation/carry schedule/sub/byte layout correspondence still explicit. Zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
anchor="mapping['library_sources'] = domain['library_sources']"
extra="\nwordContext = [pin(ROOT/'capture_source.py')] + [pin(p) for p in sorted((ROOT/'context').iterdir()) if p.is_file()]\nmapping['word_primitive_context'] = wordContext\n"
s=s.replace(anchor,anchor+extra,1)
s=s.replace("plan['pins'] += mapping['runtime_sources']", "plan['pins'] += wordContext\nplan['pins'] += mapping['runtime_sources']",1)
replace("[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', runner")
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh finite word and widened MAC source arithmetic refinement on complete 746-report/79-module qualified ancestry. No older replay or guard changes.'"+s[end:]
s=s.replace('SOURCE_SCALAR_SERIALIZATION_SYMBOLIC_RANGE_FOUR_U64_ROUNDS','SOURCE_SCALAR_FINITE_U64_INPUTS_AND_WIDENED_MAC_ARITHMETIC')
s=s.replace('SCALAR_SERIALIZATION_RANGE_COMPLETE_SEVENTY_EIGHT_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SCALAR_WORD_PRIMITIVES_COMPLETE_SEVENTY_NINE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'inherited_audits': 738", "'inherited_audits': 746")

retained = "unrunWords = DIAG/'transfer-scalar-word-primitives-20261011-01'\nplan['pins'] += [pin(unrunWords/n) for n in ['capture_source.py','prepare_recipe.py','prepare.py','handwritten/TransferScalarWordPrimitives01.lean']]\n"
s=s.replace('unique = {}', retained+'unique = {}',1)
s=s.replace("[Path(__file__), ROOT / 'prepare_recipe.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner",1)

(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':10,'inherited_reports':746,'owned_modules':79,'native_correspondence_still_open':True})
