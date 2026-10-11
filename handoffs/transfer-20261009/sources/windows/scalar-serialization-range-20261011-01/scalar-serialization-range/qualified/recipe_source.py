"""Prepare a symbolic range proof for the pinned scalar serializer reduction."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
source='''import ShielddSecurity.TransferNativeOnlyPublication01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarSerializationRange01
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Symbolic range bound for the four-round Montgomery reduction used by the
pinned BLS Scalar to_bytes implementation. The mathematical recurrence divides
the accumulated numerator by the word radix at each round, then conditionally
subtracts the modulus. No cancellation, primality or curve theorem is needed
for this range claim. Correspondence to Rust mac/adc/sbb, carry threading,
word packing and little-endian serialization is still an explicit interface.
This is a proof of the recurrence, not a native execution or certification. -/
def radix64 : Nat := 2 ^ 64

def reduceRounds (modulus radix : Nat) (accumulator : Nat) : List Nat → Nat
  | [] => accumulator
  | multiplier :: rest => reduceRounds modulus radix ((accumulator + multiplier * modulus) / radix) rest

def normalize (modulus accumulator : Nat) : Nat :=
  if modulus ≤ accumulator then accumulator - modulus else accumulator

theorem one_round_preserves_symbolic_range (modulus radix accumulator multiplier rounds : Nat)
    (positive : 0 < radix) (word : multiplier < radix)
    (initial : accumulator < modulus + radix ^ (rounds + 1)) :
    (accumulator + multiplier * modulus) / radix < modulus + radix ^ rounds := by
  apply (Nat.div_lt_iff_lt_mul positive).2
  calc
    accumulator + multiplier * modulus < (modulus + radix ^ (rounds + 1)) + multiplier * modulus := Nat.add_lt_add_right initial _
    _ = (multiplier + 1) * modulus + radix ^ rounds * radix := by
      simp only [Nat.pow_succ, Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    _ ≤ radix * modulus + radix ^ rounds * radix := Nat.add_le_add_right (Nat.mul_le_mul_right modulus (Nat.succ_le_of_lt word)) _
    _ = (modulus + radix ^ rounds) * radix := by
      rw [Nat.add_mul, Nat.mul_comm radix modulus]

theorem all_rounds_finish_at_most_modulus (modulus radix : Nat) (digits : List Nat)
    (positive : 0 < radix) (words : ∀ digit ∈ digits, digit < radix)
    (accumulator : Nat) (initial : accumulator < modulus + radix ^ digits.length) :
    reduceRounds modulus radix accumulator digits < modulus + 1 := by
  induction digits generalizing accumulator with
  | nil => simpa only [reduceRounds, List.length_nil, Nat.pow_zero] using initial
  | cons digit rest ih =>
    apply ih
    · intro next inside
      exact words next (List.mem_cons_of_mem digit inside)
    · exact one_round_preserves_symbolic_range modulus radix accumulator digit rest.length
        positive (words digit List.mem_cons_self) initial

theorem final_subtraction_is_canonical (modulus accumulator : Nat)
    (positive : 0 < modulus) (bounded : accumulator < modulus + 1) :
    normalize modulus accumulator < modulus := by
  by_cases high : modulus ≤ accumulator
  · have exactModulus : accumulator = modulus := Nat.le_antisymm (Nat.le_of_lt_succ bounded) high
    subst accumulator
    simpa only [normalize, Nat.le_refl, if_true, Nat.sub_self] using positive
  · simpa only [normalize, high, if_false] using Nat.lt_of_not_ge high

theorem finite_word_vector_reduction_is_canonical (modulus radix : Nat)
    (positiveModulus : 0 < modulus) (positiveRadix : 0 < radix)
    (digits : List (Fin radix)) (accumulator : Nat)
    (rawBound : accumulator < radix ^ digits.length) :
    normalize modulus (reduceRounds modulus radix accumulator (digits.map Fin.val)) < modulus := by
  apply final_subtraction_is_canonical modulus _ positiveModulus
  apply all_rounds_finish_at_most_modulus modulus radix (digits.map Fin.val) positiveRadix
  · intro digit inside
    obtain ⟨word, _, value⟩ := List.mem_map.mp inside
    subst digit
    exact word.isLt
  · simpa only [List.length_map] using Nat.lt_of_lt_of_le rawBound (Nat.le_add_left _ _)

theorem four_u64_rounds_reduce_into_actual_nullifier_field
    (digits : List (Fin radix64)) (four : digits.length = 4)
    (raw : Nat) (fourWords : raw < radix64 ^ 4) :
    normalize nullifierModulus (reduceRounds nullifierModulus radix64 raw (digits.map Fin.val)) < nullifierModulus := by
  apply finite_word_vector_reduction_is_canonical nullifierModulus radix64 (by decide) (by decide) digits raw
  simpa only [four] using fourWords

set_option pp.all true in
#check @radix64
#print axioms radix64
set_option pp.all true in
#check @reduceRounds
#print axioms reduceRounds
set_option pp.all true in
#check @normalize
#print axioms normalize
set_option pp.all true in
#check @one_round_preserves_symbolic_range
#print axioms one_round_preserves_symbolic_range
set_option pp.all true in
#check @all_rounds_finish_at_most_modulus
#print axioms all_rounds_finish_at_most_modulus
set_option pp.all true in
#check @final_subtraction_is_canonical
#print axioms final_subtraction_is_canonical
set_option pp.all true in
#check @finite_word_vector_reduction_is_canonical
#print axioms finite_word_vector_reduction_is_canonical
set_option pp.all true in
#check @four_u64_rounds_reduce_into_actual_nullifier_field
#print axioms four_u64_rounds_reduce_into_actual_nullifier_field
end ShielddSecurity.TransferScalarSerializationRange01
'''
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferScalarSerializationRange01.lean').write_text(source)
s=(DIAG/'transfer-native-only-publication-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-native-reachable-erasure-20261011-03'", "UPSTREAM = DIAG / 'transfer-native-only-publication-20261011-01'")
replace("POOL = DIAG / 'transfer-native-only-publication-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-scalar-serialization-range-owned-floor-20261011-02'")
replace("MODULE = 'TransferNativeOnlyPublication01'", "MODULE = 'TransferScalarSerializationRange01'")
s=s.replace("'runs/01-TransferNativeReachableErasure01/stdout.txt'", "'runs/01-TransferNativeOnlyPublication01/stdout.txt'",1)
replace('assert len(current) == 4','assert len(current) == 1')
replace("records.append(('TransferNativeReachableErasure01'", "records.append(('TransferNativeOnlyPublication01'")
replace("    'handwritten/TransferNativeReachableErasure01.lean', 'project/ShielddSecurity/TransferNativeReachableErasure01.lean']]", "    'handwritten/TransferNativeOnlyPublication01.lean', 'project/ShielddSecurity/TransferNativeOnlyPublication01.lean']]")
replace('assert len(records) == 77 and len(audits) == 737','assert len(records) == 78 and len(audits) == 738')
replace("'objects': 77", "'objects': 78")
s=s.replace('seventy-seven-module','seventy-eight-module').replace('737 inherited','738 inherited')
replace("'imports': ['ShielddSecurity.TransferNativeReachableErasure01']", "'imports': ['ShielddSecurity.TransferNativeOnlyPublication01']")
replace('assert len(names) == 1','assert len(names) == 8')
replace("'fresh_audits': 1", "'fresh_audits': 8")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Symbolic radix recurrence proves canonical final range after four u64 rounds and one conditional modulus subtraction for the exact accepted nullifier field modulus. Generic small induction works for arbitrary finite word vectors without unrolled constraint walks. The pinned BLS Scalar to_bytes/montgomery_reduce/sub source has the corresponding four-round source structure; primitive machine-word arithmetic, carries, packing and little-endian byte correspondence remain explicit interfaces. Eight full reports, three definitions and five theorems. Source association and identity do not certify native semantics. Zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh symbolic scalar serialization range obligation on exact qualified 738-report/78-module ancestry. Old sources/proofs immutable and reused without replay; all physical/per-run guards unchanged.'"+s[end:]
s=s.replace('SOURCE_NATIVE_ONLY_DEFAULT_WALK_SINGLE_REACHED_GETTER_WHOLE_PUBLICATION','SOURCE_SCALAR_SERIALIZATION_SYMBOLIC_RANGE_FOUR_U64_ROUNDS')
s=s.replace('NATIVE_ONLY_PUBLICATION_COMPLETE_SEVENTY_SEVEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SCALAR_SERIALIZATION_RANGE_COMPLETE_SEVENTY_EIGHT_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'inherited_audits': 737", "'inherited_audits': 738")

failedPins = "failed_scalar = DIAG / 'transfer-scalar-serialization-range-20261011-01'\nplan['pins'] += [pin(failed_scalar/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarSerializationRange01.lean','project/ShielddSecurity/TransferScalarSerializationRange01.lean','runs/01-TransferScalarSerializationRange01/stdout.txt']]\n"
s=s.replace('unique = {}', failedPins + 'unique = {}', 1)
s=s.replace("[Path(__file__), ROOT / 'prepare_recipe.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner", 1)
s=s.replace('Fresh symbolic scalar serialization range obligation', 'Proof-only distributivity repair of scalar range01; all eight declaration statements unchanged; failed01 complete raw diagnostics retained with zero credit. Fresh symbolic scalar serialization range obligation')

(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':8,'inherited_reports':738,'owned_modules':78,'native_correspondence_still_open':True})
