"""Derive serializer reduction range from the actual finite carry walk and source constants."""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
domainPath=DIAG/'transfer-bounded-native-codec-20261011-02/context/canonical-domain.json'
domain=json.loads(domainPath.read_bytes())
scalar=Path(next(r['path'] for r in domain['library_sources'] if r['path'].endswith('-scalar.rs')))
scalarRow=next(r for r in domain['library_sources'] if r['path']==str(scalar))
assert hashlib.sha256(scalar.read_bytes()).hexdigest()==scalarRow['sha256']
text=scalar.read_text()
inverse=re.search(r'const INV: u64 = (0x[0-9a-f_]+);',text).group(1)
assert inverse=='0xffff_fffe_ffff_ffff'
assert 'Scalar::montgomery_reduce(self.0[0], self.0[1], self.0[2], self.0[3], 0, 0, 0, 0)' in text
section=text[text.index('    const fn montgomery_reduce('):text.index('    /// Multiplies `rhs`',text.index('    const fn montgomery_reduce('))]
assert len(re.findall(r'let k = r[0-3]\.wrapping_mul\(INV\);',section))==4
assert len(re.findall(r'= mac\(',section))==16 and len(re.findall(r'= adc\(',section))==4
assert '(&Scalar([r4, r5, r6, r7])).sub(&MODULUS)' in section
limbs='['+', '.join('0x'+s for s in domain['limbs'])+']'
(ROOT/'context').mkdir()
association={'kind':'SOURCE_SCALAR_TO_BYTES_FOUR_ROUND_SHAPE_AND_CONSTANTS','scalar_source':scalarRow,'modulus_limbs':domain['limbs'],'inverse':inverse,'to_bytes_high_limbs_zero':True,'rounds':4,'mac_calls':16,'adc_calls':4,'final_subtraction':True,'scope':'Exact pinned source structure and constants only; no semantic correspondence or executed native/control credit. Wrapper uses generic finite carry loop for four rounds. Actual Rust primitive/ADC/SBB/byte semantics remain interfaces.'}
(ROOT/'context/source-association.json').write_text(json.dumps(association,indent=2,sort_keys=True)+'\n')
source='''import ShielddSecurity.TransferScalarCarrySchedule01
import Init.Data.List.Zip
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarFourRoundWrapper01
open TransferScalarSerializationRange01 (radix64 reduceRounds normalize)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarCarrySchedule01 (macLoop dropLowAndAppendCarry)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Four-round finite carry wrapper derived from pinned Scalar source constants.
Each actual model multiplier is the wrapping UInt64 product of the current low
word and INV. The carry walk, low-word drop and retained carry derive the Nat
quotient recurrence. The canonical range follows from finite raw UInt64 input;
no input-field-range or caller-provided multiplier list premise is supplied.
Source shape/identity is separate from Rust primitive/ADC/SBB/byte/trace
correspondence; top zero limbs in to_bytes motivate carry appending here. -/
def modulusWords : List UInt64 := __LIMBS__
def inverseWord : UInt64 := __INVERSE__
def nativeRound (words : List UInt64) : List UInt64 :=
  dropLowAndAppendCarry (macLoop (words.headD 0 * inverseWord) 0 (words.zip modulusWords))
def nativeRounds : Nat → List UInt64 → List UInt64
  | 0, words => words
  | rounds + 1, words => nativeRounds rounds (nativeRound words)
def roundMultipliers : Nat → List UInt64 → List Nat
  | 0, _ => []
  | rounds + 1, words => (words.headD 0 * inverseWord).toNat :: roundMultipliers rounds (nativeRound words)

theorem modulus_words_have_four_limbs : modulusWords.length = 4 := rfl
theorem modulus_words_pack_to_actual_nullifier_modulus : packWords modulusWords = nullifierModulus := by decide

theorem one_native_round_preserves_four_word_width (words : List UInt64) (four : words.length = 4) :
    (nativeRound words).length = 4 := by
  have zipped : (words.zip modulusWords).length = 4 := by
    rw [List.length_zip, four, modulus_words_have_four_limbs, Nat.min_self]
  change ((macLoop (words.headD 0 * inverseWord) 0 (words.zip modulusWords)).1.drop 1 ++
    [(macLoop (words.headD 0 * inverseWord) 0 (words.zip modulusWords)).2]).length = 4
  rw [List.length_append, List.length_drop, TransferScalarCarrySchedule01.carry_walk_retains_limb_count,
    zipped]
  rfl

theorem one_native_round_packs_to_derived_radix_quotient (words : List UInt64) (four : words.length = 4) :
    packWords (nativeRound words) =
      (packWords words + (words.headD 0 * inverseWord).toNat * nullifierModulus) / radix64 := by
  have zipped : (words.zip modulusWords).length = 4 := by
    rw [List.length_zip, four, modulus_words_have_four_limbs, Nat.min_self]
  have nonempty : words.zip modulusWords ≠ [] := by
    intro empty
    rw [empty, List.length_nil] at zipped
    cases zipped
  have firstProjection : words.length ≤ modulusWords.length := by
    rw [four, modulus_words_have_four_limbs]
    exact Nat.le_refl 4
  have secondProjection : modulusWords.length ≤ words.length := by
    rw [four, modulus_words_have_four_limbs]
    exact Nat.le_refl 4
  have result := TransferScalarCarrySchedule01.nonempty_mac_walk_drops_to_exact_quotient
    (words.headD 0 * inverseWord) 0 (words.zip modulusWords) nonempty
  rw [List.map_fst_zip firstProjection, List.map_snd_zip secondProjection,
    modulus_words_pack_to_actual_nullifier_modulus, UInt64.toNat_zero, Nat.add_zero] at result
  exact result

theorem native_round_walk_preserves_four_word_width (rounds : Nat) (words : List UInt64)
    (four : words.length = 4) : (nativeRounds rounds words).length = 4 := by
  induction rounds generalizing words with
  | zero => exact four
  | succ rounds ih => exact ih (nativeRound words) (one_native_round_preserves_four_word_width words four)

theorem derived_multiplier_vector_has_round_count (rounds : Nat) (words : List UInt64) :
    (roundMultipliers rounds words).length = rounds := by
  induction rounds generalizing words with
  | zero => rfl
  | succ rounds ih =>
    change (roundMultipliers rounds (nativeRound words)).length + 1 = rounds + 1
    rw [ih]

theorem every_derived_multiplier_is_a_finite_u64_word (rounds : Nat) (words : List UInt64) :
    ∀ digit ∈ roundMultipliers rounds words, digit < radix64 := by
  induction rounds generalizing words with
  | zero => intro digit inside; cases inside
  | succ rounds ih =>
    intro digit inside
    cases inside with
    | head => exact (words.headD 0 * inverseWord).toNat_lt
    | tail _ inside => exact ih (nativeRound words) digit inside

theorem native_carry_rounds_pack_to_symbolic_reduction (rounds : Nat) (words : List UInt64)
    (four : words.length = 4) :
    packWords (nativeRounds rounds words) =
      reduceRounds nullifierModulus radix64 (packWords words) (roundMultipliers rounds words) := by
  induction rounds generalizing words with
  | zero => rfl
  | succ rounds ih =>
    change packWords (nativeRounds rounds (nativeRound words)) =
      reduceRounds nullifierModulus radix64
        ((packWords words + (words.headD 0 * inverseWord).toNat * nullifierModulus) / radix64)
        (roundMultipliers rounds (nativeRound words))
    rw [← one_native_round_packs_to_derived_radix_quotient words four]
    exact ih (nativeRound words) (one_native_round_preserves_four_word_width words four)

theorem actual_four_round_carry_wrapper_normalizes_into_canonical_nullifier_field
    (words : List UInt64) (four : words.length = 4) :
    normalize nullifierModulus (packWords (nativeRounds 4 words)) < nullifierModulus := by
  apply TransferScalarSerializationRange01.final_subtraction_is_canonical nullifierModulus _ (by decide)
  rw [native_carry_rounds_pack_to_symbolic_reduction 4 words four]
  apply TransferScalarSerializationRange01.all_rounds_finish_at_most_modulus nullifierModulus radix64
    (roundMultipliers 4 words) (by decide) (every_derived_multiplier_is_a_finite_u64_word 4 words)
  rw [derived_multiplier_vector_has_round_count]
  have raw := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power words
  rw [four] at raw
  exact Nat.lt_of_lt_of_le raw (Nat.le_add_left _ _)

'''.replace('__LIMBS__',limbs).replace('__INVERSE__',inverse)
names=['modulusWords','inverseWord','nativeRound','nativeRounds','roundMultipliers','modulus_words_have_four_limbs','modulus_words_pack_to_actual_nullifier_modulus','one_native_round_preserves_four_word_width','one_native_round_packs_to_derived_radix_quotient','native_round_walk_preserves_four_word_width','derived_multiplier_vector_has_round_count','every_derived_multiplier_is_a_finite_u64_word','native_carry_rounds_pack_to_symbolic_reduction','actual_four_round_carry_wrapper_normalizes_into_canonical_nullifier_field']
for name in names:
    source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferScalarFourRoundWrapper01\n'
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferScalarFourRoundWrapper01.lean').write_text(source)
s=(DIAG/'transfer-scalar-carry-schedule-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-scalar-word-primitives-20261011-03'", "UPSTREAM = DIAG / 'transfer-scalar-carry-schedule-20261011-02'")
replace("POOL = DIAG / 'transfer-scalar-carry-schedule-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-scalar-four-round-wrapper-owned-floor-20261011-02'")
replace("MODULE = 'TransferScalarCarrySchedule01'", "MODULE = 'TransferScalarFourRoundWrapper01'")
s=s.replace("'runs/01-TransferScalarWordPrimitives01/stdout.txt'", "'runs/01-TransferScalarCarrySchedule01/stdout.txt'",1)
replace('assert len(current) == 10','assert len(current) == 7')
replace("records.append(('TransferScalarWordPrimitives01'", "records.append(('TransferScalarCarrySchedule01'")
replace("    'handwritten/TransferScalarWordPrimitives01.lean', 'project/ShielddSecurity/TransferScalarWordPrimitives01.lean']]", "    'handwritten/TransferScalarCarrySchedule01.lean', 'project/ShielddSecurity/TransferScalarCarrySchedule01.lean']]")
replace('assert len(records) == 80 and len(audits) == 756','assert len(records) == 81 and len(audits) == 763')
replace("'objects': 80", "'objects': 81")
s=s.replace('eighty-module','eighty-one-module').replace('756 inherited','763 inherited')
replace("'imports': ['ShielddSecurity.TransferScalarWordPrimitives01']", "'imports': ['ShielddSecurity.TransferScalarCarrySchedule01','Init.Data.List.Zip']")
replace('assert len(names) == 7','assert len(names) == 14')
replace("'fresh_audits': 7", "'fresh_audits': 14")
replace("[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', runner")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Five finite-word serializer wrapper definitions and nine small symbolic theorems: exact source-extracted modulus limbs/INV, actual model current-low-word wrapping multiplier, carry-chain/drop quotient for each four-word stage, four-word width preservation, derived multiplier widths/count, equality with symbolic Nat reduction, and canonical field range for normalized actual four-round carry wrapper from arbitrary four UInt64 inputs. Fourteen full reports on complete qualified closure. Pinned to_bytes zero-high-limb source shape/four groups/16MAC/4ADC/final sub statically checked; source identity/shape is not Rust primitive/ADC/SBB/endian/trace correspondence. Zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
anchor="mapping['word_primitive_context'] = wordContext"
s=s.replace(anchor,anchor+"\nmapping['serializer_wrapper_source_association'] = pin(ROOT/'context/source-association.json')",1)
s=s.replace("plan['pins'] += wordContext", "plan['pins'] += wordContext + [mapping['serializer_wrapper_source_association']]",1)
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh source-constant four-round finite carry wrapper range and Nat recurrence refinement; qualified carry02 seven reports reused on complete 763-report/81-module ancestry without replay; historical diagnostics and all guards unchanged.'"+s[end:]
s=s.replace('SOURCE_SCALAR_SYMBOLIC_CARRY_SCHEDULE_AND_LOW_LIMB_QUOTIENT','SOURCE_SCALAR_FOUR_ROUND_FINITE_CARRY_WRAPPER_CANONICAL_RANGE')
s=s.replace('SCALAR_CARRY_SCHEDULE_COMPLETE_EIGHTY_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SCALAR_FOUR_ROUND_WRAPPER_COMPLETE_EIGHTY_ONE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'inherited_audits': 756", "'inherited_audits': 763")

retained = "failedWrapper = DIAG/'transfer-scalar-four-round-wrapper-20261011-01'\nplan['pins'] += [pin(failedWrapper/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/source-association.json','handwritten/TransferScalarFourRoundWrapper01.lean','project/ShielddSecurity/TransferScalarFourRoundWrapper01.lean','runs/01-TransferScalarFourRoundWrapper01/stdout.txt']]\n"
s=s.replace('unique = {}', retained+'unique = {}',1)
s=s.replace("[Path(__file__), ROOT / 'prepare_recipe.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner",1)
s=s.replace('Fresh source-constant four-round finite carry wrapper range', 'Fresh02 proof-only closure of two rewritten reflexive inequalities; all fourteen declaration contracts unchanged, failed01 full raw diagnostics retained with zero credit. Fresh source-constant four-round finite carry wrapper range')

(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':14,'inherited_reports':763,'owned_modules':81,'native_correspondence_still_open':True})
