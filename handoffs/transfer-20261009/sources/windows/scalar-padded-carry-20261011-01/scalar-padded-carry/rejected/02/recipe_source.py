"""Symbolic exact zero-padded source MAC/ADC schedule, all ignored ADC carries derived zero."""
import re
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
source='''import ShielddSecurity.TransferTypedScalarPublication01
import ShielddSecurity.TransferScalarAdcShift01
import Init.Data.List.Nat.TakeDrop
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarPaddedCarry01
open TransferScalarFourRoundWrapper01 (modulusWords inverseWord nativeRound nativeRounds)
open TransferScalarCarrySchedule01 (macLoop)
open TransferScalarAdcShift01 (adc64)
open TransferScalarMaskedNormalization01 (sourceNormalize)
open TransferScalarLittleEndianBytes01 (wordsBytes decodeLE serializerBytes scalarKey)
open TransferScalarMontgomeryValue01 (montgomeryValue)
/-! Source-shaped zero-padded scalar serializer reduction. Each round executes
the four low-limb MACs then the actual finite ADC on the next padded limb,
retains its low result and explicitly records its ignored outgoing carry.
Symbolic list induction derives fixed-width carry-wrapper equality and zero
for every ignored carry from the actual padded words, without a desired carry
premise. The exact four-round 32-byte canonical Montgomery result follows.
Pinned Rust constants/four-MAC/ADC/zero-high source shape is retained;
Rust primitive/trace/compiler/type/field bindings remain separate interfaces. -/

def paddedRound (words : List UInt64) : List UInt64 × UInt64 :=
  let low := words.take 4
  let mac := macLoop (low.headD 0 * inverseWord) 0 (low.zip modulusWords)
  let upper := adc64 ((words.drop 4).headD 0) 0 mac.2
  (mac.1.drop 1 ++ [upper.1] ++ words.drop 5, upper.2)

def paddedRounds : Nat → List UInt64 → List UInt64
  | 0, words => words
  | rounds + 1, words => paddedRounds rounds (paddedRound words).1

def paddedNoOverflow : Nat → List UInt64 → Prop
  | 0, _ => True
  | rounds + 1, words => (paddedRound words).2 = 0 ∧ paddedNoOverflow rounds (paddedRound words).1

theorem source_padded_round_is_exact_carry_wrapper_and_zero_ignored_carry
    (words tail : List UInt64) (four : words.length = 4) :
    paddedRound (words ++ 0 :: tail) = (nativeRound words ++ tail, 0) := by
  have taken : (words ++ 0 :: tail).take 4 = words := by
    rw [← four, List.take_append_length]
  have dropped : (words ++ 0 :: tail).drop 4 = 0 :: tail := by
    rw [← four, List.drop_append_length]
  have rest : (words ++ 0 :: tail).drop 5 = tail := by
    have width : 5 = words.length + 1 := by omega
    rw [width, List.drop_length_add_append]
    rfl
  unfold paddedRound
  rw [taken, dropped, rest, List.headD_cons,
    TransferScalarAdcShift01.zero_upper_limb_adc_retains_carry_without_overflow]
  rfl

theorem symbolic_zero_padded_walk_derives_fixed_wrapper_and_all_zero_ignored_carries
    (rounds : Nat) (words : List UInt64) (four : words.length = 4) :
    paddedRounds rounds (words ++ List.replicate rounds 0) = nativeRounds rounds words ∧
      paddedNoOverflow rounds (words ++ List.replicate rounds 0) := by
  induction rounds generalizing words with
  | zero => simp only [List.replicate_zero, List.append_nil, paddedRounds, nativeRounds, paddedNoOverflow, and_self]
  | succ rounds ih =>
    change paddedRounds rounds (paddedRound (words ++ List.replicate (rounds + 1) 0)).1 =
      nativeRounds rounds (nativeRound words) ∧
      (paddedRound (words ++ List.replicate (rounds + 1) 0)).2 = 0 ∧
      paddedNoOverflow rounds (paddedRound (words ++ List.replicate (rounds + 1) 0)).1
    rw [List.replicate_succ, source_padded_round_is_exact_carry_wrapper_and_zero_ignored_carry words _ four]
    have remaining := ih (nativeRound words)
      (TransferScalarFourRoundWrapper01.one_native_round_preserves_four_word_width words four)
    exact ⟨remaining.1, rfl, remaining.2⟩

theorem four_round_zero_padded_source_serializer_has_exact_width_and_montgomery_value
    (words : Vector UInt64 4) :
    (wordsBytes (sourceNormalize (paddedRounds 4 (words.toList ++ List.replicate 4 0)))).length = 32 ∧
      decodeLE (wordsBytes (sourceNormalize (paddedRounds 4 (words.toList ++ List.replicate 4 0)))) =
        montgomeryValue words ∧
      paddedNoOverflow 4 (words.toList ++ List.replicate 4 0) := by
  have reduced := symbolic_zero_padded_walk_derives_fixed_wrapper_and_all_zero_ignored_carries
    4 words.toList Vector.length_toList
  rw [reduced.1]
  exact ⟨TransferScalarLittleEndianBytes01.source_scalar_serialization_has_exact_32_byte_width
      words.toList Vector.length_toList,
    TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value words,
    reduced.2⟩

'''
names=re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',source,re.M)
assert len(names)==6
for name in names:
    source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferScalarPaddedCarry01\n'
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferScalarPaddedCarry01.lean').write_text(source)
s=(DIAG/'transfer-typed-scalar-publication-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-scalar-montgomery-value-20261011-03'", "UPSTREAM = DIAG / 'transfer-typed-scalar-publication-20261011-01'")
replace("POOL = DIAG / 'transfer-typed-scalar-publication-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-scalar-padded-carry-owned-floor-20261011-02'")
replace("MODULE = 'TransferTypedScalarPublication01'", "MODULE = 'TransferScalarPaddedCarry01'")
s=s.replace("'runs/01-TransferScalarMontgomeryValue01/stdout.txt'", "'runs/01-TransferTypedScalarPublication01/stdout.txt'",1)
replace('assert len(current) == 13','assert len(current) == 3')
replace("records.append(('TransferScalarMontgomeryValue01'", "records.append(('TransferTypedScalarPublication01'")
replace("    'handwritten/TransferScalarMontgomeryValue01.lean', 'project/ShielddSecurity/TransferScalarMontgomeryValue01.lean']]", "    'handwritten/TransferTypedScalarPublication01.lean', 'project/ShielddSecurity/TransferTypedScalarPublication01.lean']]")
replace('assert len(records) == 88 and len(audits) == 839','assert len(records) == 89 and len(audits) == 842')
replace("'objects': 88", "'objects': 89")
s=s.replace('eighty-eight-module','eighty-nine-module').replace('839 inherited','842 inherited')
replace("'imports': ['ShielddSecurity.TransferScalarMontgomeryValue01','ShielddSecurity.TransferNativeOnlyPublication01']", "'imports': ['ShielddSecurity.TransferTypedScalarPublication01','ShielddSecurity.TransferScalarAdcShift01','Init.Data.List.Nat.TakeDrop']")
replace('assert len(names) == 3','assert len(names) == 6')
replace("'fresh_audits': 3", "'fresh_audits': 6")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Explicit finite source-shaped padded four-MAC/next-upper-limb ADC round records ignored outgoing carry; symbolic padding induction proves every ignored carry zero and exact fixed-width native carry wrapper. Four-round source zero-high serializer has exact 32-byte width and canonical mathematical Montgomery value. Six complete reports: three definitions/three theorems. No desired carry/output premise, finite reusable list recurrence, no wide constraint walk. Exact pinned constants/zero-high/four-MAC/ADC structure retained; actual Rust primitive/trace/compiler/type/field/library/native projection remain separate correspondence obligations. Zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh explicit source padded MAC/ADC schedule on exact 842-report/89-module qualified ancestry. Symbolic padded list recurrence derives zero ignored carries and fixed-width wrapper, exact canonical serializer; all guards unchanged and no ancestor replay.'"+s[end:]
s=s.replace('SOURCE_TYPED_SCALAR_EXACT_PUBLICATION_JOIN','SOURCE_SCALAR_EXPLICIT_PADDED_MAC_ADC_CARRY_SCHEDULE')
s=s.replace('TYPED_SCALAR_PUBLICATION_COMPLETE_EIGHTY_EIGHT_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SCALAR_PADDED_CARRY_COMPLETE_EIGHTY_NINE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'inherited_audits': 839", "'inherited_audits': 842")

retained = "pressureStopped = DIAG/'transfer-scalar-padded-carry-20261011-01'\nplan['pins'] += [pin(pressureStopped/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarPaddedCarry01.lean','project/ShielddSecurity/TransferScalarPaddedCarry01.lean']]\n"
s=s.replace('unique = {}',retained+'unique = {}',1)
s=s.replace("[Path(__file__), ROOT / 'prepare_recipe.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner",1)
s=s.replace('Fresh explicit source padded MAC/ADC schedule', 'Fresh02 identical source after failed01 physical-memory monitor stopped its owned job. Failed01 exact source/plan/events retained, no stdout saved before interruption, zero proof/control credit. All guards unchanged. Fresh explicit source padded MAC/ADC schedule')

(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':6,'inherited_reports':842,'owned_modules':89,'native_correspondence_still_open':True})
