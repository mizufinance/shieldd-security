"""Prove finite SBB/subtract and borrow-masked ADC add-back implement modulus normalization."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
source='''import ShielddSecurity.TransferScalarBorrowWalk01
import Init.Data.UInt.Bitwise
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarMaskedNormalization01
open TransferScalarSerializationRange01 (radix64 normalize)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarCarrySchedule01 (macLoop)
open TransferScalarBorrowWalk01 (borrowWalk)
open TransferScalarSbbPrimitive01 (borrowMask borrowBit)
open TransferScalarFourRoundWrapper01 (modulusWords nativeRounds)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Source-shaped four-limb sub and borrow-masked ADC add-back. Final borrow
is derived from the exact SBB walk; each modulus limb uses actual UInt64 AND
with the source zero/all-ones mask. The retained low vector of the widened
unit MAC (ADC equivalent) implements normalization, with final carry discarded.
Source model range is derived from four finite raw words and the actual carry
wrapper; no desired underflow/result is supplied. Rust trace/endian remain interfaces. -/
def maskedModulus (borrow : Bool) : List UInt64 := modulusWords.map (fun word => word &&& borrowMask borrow)
def sourceNormalize (words : List UInt64) : List UInt64 :=
  let difference := borrowWalk false (words.zip modulusWords)
  (macLoop 1 0 (difference.1.zip (maskedModulus difference.2))).1

theorem word_and_reachable_borrow_mask_selects_exact_operand (word : UInt64) (borrow : Bool) :
    word &&& borrowMask borrow = if borrow then word else 0 := by
  cases borrow with
  | false => change word &&& 0 = 0; exact UInt64.and_zero
  | true => change word &&& (-1 : UInt64) = word; exact UInt64.and_neg_one

theorem packing_masked_word_vector_selects_exact_value (words : List UInt64) (borrow : Bool) :
    packWords (words.map (fun word => word &&& borrowMask borrow)) = if borrow then packWords words else 0 := by
  induction words generalizing borrow with
  | nil => cases borrow <;> rfl
  | cons word rest ih =>
    cases borrow with
    | false =>
      change (word &&& borrowMask false).toNat + radix64 * packWords (rest.map (fun word => word &&& borrowMask false)) = 0
      rw [word_and_reachable_borrow_mask_selects_exact_operand, ih false]
      rfl
    | true =>
      change (word &&& borrowMask true).toNat + radix64 * packWords (rest.map (fun word => word &&& borrowMask true)) = packWords (word :: rest)
      rw [word_and_reachable_borrow_mask_selects_exact_operand, ih true]
      rfl

theorem masked_modulus_retains_four_limb_width (borrow : Bool) : (maskedModulus borrow).length = 4 := by
  rw [maskedModulus, List.length_map, TransferScalarFourRoundWrapper01.modulus_words_have_four_limbs]

theorem masked_modulus_packs_to_exact_selected_modulus (borrow : Bool) :
    packWords (maskedModulus borrow) = if borrow then nullifierModulus else 0 := by
  rw [maskedModulus, packing_masked_word_vector_selects_exact_value,
    TransferScalarFourRoundWrapper01.modulus_words_pack_to_actual_nullifier_modulus]

theorem unit_mac_low_vector_is_full_sum_modulo_radix_power (pairs : List (UInt64 × UInt64)) :
    packWords (macLoop 1 0 pairs).1 =
      (packWords (pairs.map Prod.fst) + packWords (pairs.map Prod.snd)) % radix64 ^ pairs.length := by
  have conserved := TransferScalarCarrySchedule01.carry_walk_conserves_full_integer 1 0 pairs
  have bounded := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power (macLoop 1 0 pairs).1
  rw [TransferScalarCarrySchedule01.carry_walk_retains_limb_count] at bounded
  simp only [UInt64.toNat_one, UInt64.toNat_zero, Nat.one_mul, Nat.add_zero] at conserved
  rw [← conserved, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt bounded]

theorem source_normalization_retains_four_word_width (words : List UInt64) (four : words.length = 4) :
    (sourceNormalize words).length = 4 := by
  have zipped : (words.zip modulusWords).length = 4 := by
    rw [List.length_zip, four, TransferScalarFourRoundWrapper01.modulus_words_have_four_limbs, Nat.min_self]
  have difference : (borrowWalk false (words.zip modulusWords)).1.length = 4 := by
    rw [TransferScalarBorrowWalk01.borrow_walk_retains_limb_count, zipped]
  unfold sourceNormalize
  rw [TransferScalarCarrySchedule01.carry_walk_retains_limb_count, List.length_zip, difference,
    masked_modulus_retains_four_limb_width, Nat.min_self]

theorem source_sub_and_masked_addback_equal_single_modulus_normalization
    (words : List UInt64) (four : words.length = 4) :
    packWords (sourceNormalize words) = normalize nullifierModulus (packWords words) := by
  let pairs := words.zip modulusWords
  let difference := borrowWalk false pairs
  have zipped : pairs.length = 4 := by
    rw [List.length_zip, four, TransferScalarFourRoundWrapper01.modulus_words_have_four_limbs, Nat.min_self]
  have firstProjection : words.length ≤ modulusWords.length := by
    rw [four, TransferScalarFourRoundWrapper01.modulus_words_have_four_limbs]
    exact Nat.le_refl 4
  have secondProjection : modulusWords.length ≤ words.length := by
    rw [four, TransferScalarFourRoundWrapper01.modulus_words_have_four_limbs]
    exact Nat.le_refl 4
  have differenceFour : difference.1.length = 4 := by
    rw [TransferScalarBorrowWalk01.borrow_walk_retains_limb_count, zipped]
  have addWidth : (difference.1.zip (maskedModulus difference.2)).length = 4 := by
    rw [List.length_zip, differenceFour, masked_modulus_retains_four_limb_width, Nat.min_self]
  have addFirst : difference.1.length ≤ (maskedModulus difference.2).length := by
    rw [differenceFour, masked_modulus_retains_four_limb_width]
    exact Nat.le_refl 4
  have addSecond : (maskedModulus difference.2).length ≤ difference.1.length := by
    rw [differenceFour, masked_modulus_retains_four_limb_width]
    exact Nat.le_refl 4
  have conserved := TransferScalarBorrowWalk01.borrow_walk_conserves_full_subtraction_equation false pairs
  have underflow := TransferScalarBorrowWalk01.final_borrow_is_exact_input_underflow pairs
  have added := unit_mac_low_vector_is_full_sum_modulo_radix_power (difference.1.zip (maskedModulus difference.2))
  have differenceBound := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power difference.1
  have rawBound := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power words
  rw [differenceFour] at differenceBound
  rw [four] at rawBound
  rw [List.map_fst_zip firstProjection, List.map_snd_zip secondProjection,
    TransferScalarFourRoundWrapper01.modulus_words_pack_to_actual_nullifier_modulus, zipped] at conserved
  rw [List.map_fst_zip firstProjection, List.map_snd_zip secondProjection,
    TransferScalarFourRoundWrapper01.modulus_words_pack_to_actual_nullifier_modulus] at underflow
  rw [List.map_fst_zip addFirst, List.map_snd_zip addSecond, masked_modulus_packs_to_exact_selected_modulus, addWidth] at added
  change packWords (macLoop 1 0 (difference.1.zip (maskedModulus difference.2))).1 = normalize nullifierModulus (packWords words)
  change packWords difference.1 + nullifierModulus + borrowBit false =
    packWords words + radix64 ^ 4 * borrowBit difference.2 at conserved
  change difference.2 = true ↔ packWords words < nullifierModulus at underflow
  cases final : difference.2 with
  | false =>
    simp [borrowBit, final] at conserved added
    have enough : nullifierModulus ≤ packWords words := by omega
    have subtracted : packWords difference.1 = packWords words - nullifierModulus := Nat.eq_sub_of_add_eq conserved
    rw [normalize, if_pos enough, added, Nat.mod_eq_of_lt differenceBound, subtracted]
  | true =>
    simp [borrowBit, final] at conserved added
    have smaller : packWords words < nullifierModulus := underflow.mp final
    rw [normalize, if_neg (Nat.not_le_of_gt smaller), added, conserved, Nat.add_mod_right, Nat.mod_eq_of_lt rawBound]

theorem four_round_source_sub_and_addback_have_canonical_field_range
    (words : List UInt64) (four : words.length = 4) :
    packWords (sourceNormalize (nativeRounds 4 words)) < nullifierModulus := by
  rw [source_sub_and_masked_addback_equal_single_modulus_normalization _
    (TransferScalarFourRoundWrapper01.native_round_walk_preserves_four_word_width 4 words four)]
  exact TransferScalarFourRoundWrapper01.actual_four_round_carry_wrapper_normalizes_into_canonical_nullifier_field words four

'''
names=['maskedModulus','sourceNormalize','word_and_reachable_borrow_mask_selects_exact_operand','packing_masked_word_vector_selects_exact_value','masked_modulus_retains_four_limb_width','masked_modulus_packs_to_exact_selected_modulus','unit_mac_low_vector_is_full_sum_modulo_radix_power','source_normalization_retains_four_word_width','source_sub_and_masked_addback_equal_single_modulus_normalization','four_round_source_sub_and_addback_have_canonical_field_range']
for name in names:
    source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferScalarMaskedNormalization01\n'
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferScalarMaskedNormalization01.lean').write_text(source)
s=(DIAG/'transfer-scalar-borrow-walk-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-scalar-sbb-primitive-20261011-02'", "UPSTREAM = DIAG / 'transfer-scalar-borrow-walk-20261011-01'")
replace("POOL = DIAG / 'transfer-scalar-borrow-walk-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-scalar-masked-normalization-owned-floor-20261011-02'")
replace("MODULE = 'TransferScalarBorrowWalk01'", "MODULE = 'TransferScalarMaskedNormalization01'")
s=s.replace("'runs/01-TransferScalarSbbPrimitive01/stdout.txt'", "'runs/01-TransferScalarBorrowWalk01/stdout.txt'",1)
replace('assert len(current) == 9','assert len(current) == 7')
replace("records.append(('TransferScalarSbbPrimitive01'", "records.append(('TransferScalarBorrowWalk01'")
replace("    'handwritten/TransferScalarSbbPrimitive01.lean', 'project/ShielddSecurity/TransferScalarSbbPrimitive01.lean']]", "    'handwritten/TransferScalarBorrowWalk01.lean', 'project/ShielddSecurity/TransferScalarBorrowWalk01.lean']]")
replace('assert len(records) == 84 and len(audits) == 794','assert len(records) == 85 and len(audits) == 801')
replace("'objects': 84", "'objects': 85")
s=s.replace('eighty-four-module','eighty-five-module').replace('794 inherited','801 inherited')
replace("'imports': ['ShielddSecurity.TransferScalarSbbPrimitive01']", "'imports': ['ShielddSecurity.TransferScalarBorrowWalk01','Init.Data.UInt.Bitwise']")
replace('assert len(names) == 7','assert len(names) == 10')
replace("'fresh_audits': 7", "'fresh_audits': 10")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Source-shaped four-limb SBB/subtract and UInt64 borrow-mask AND followed by widened unit MAC/ADC add-back prove exact single modulus normalization for every four-word finite input. Final borrow and output are derived; unit MAC truncated low vector equals full sum modulo radix power. Width retained, four actual current-low-word carry rounds plus source masked sub/add-back pack below exact nullifier modulus. Ten full reports: two definitions/eight theorems. Actual Rust trace/byte/endian/field semantic correspondence remains separate. Zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh source-shaped masked SBB/ADC normalization join on complete 801-report/85-module ancestry. Prior exact finite arithmetic/borrow/carry proofs reused without replay; historical diagnostics and all guards unchanged.'"+s[end:]
s=s.replace('SOURCE_SCALAR_SYMBOLIC_BORROW_WALK_AND_DERIVED_FINAL_UNDERFLOW','SOURCE_SCALAR_MASKED_SUBTRACTION_ADD_BACK_EXACT_NORMALIZATION')
s=s.replace('SCALAR_BORROW_WALK_COMPLETE_EIGHTY_FOUR_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SCALAR_MASKED_NORMALIZATION_COMPLETE_EIGHTY_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'inherited_audits': 794", "'inherited_audits': 801")

retained = "failedNormalization = DIAG/'transfer-scalar-masked-normalization-20261011-01'\nplan['pins'] += [pin(failedNormalization/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarMaskedNormalization01.lean','project/ShielddSecurity/TransferScalarMaskedNormalization01.lean','runs/01-TransferScalarMaskedNormalization01/stdout.txt']]\n"
s=s.replace('unique = {}', retained+'unique = {}',1)
s=s.replace("[Path(__file__), ROOT / 'prepare_recipe.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner",1)
s=s.replace('Fresh source-shaped masked SBB/ADC normalization join', 'Fresh02 proof-only actual returned-difference projection normalization before borrow cases; all ten contracts unchanged, failed01 full raw diagnostics retained with zero credit. Fresh source-shaped masked SBB/ADC normalization join')

(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':10,'inherited_reports':801,'owned_modules':85,'native_correspondence_still_open':True})
