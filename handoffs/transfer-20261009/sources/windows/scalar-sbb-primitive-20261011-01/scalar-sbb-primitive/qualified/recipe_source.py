"""Prove source-shaped 128-bit wrapping subtraction yields a low word and exact borrow mask."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
source='''import ShielddSecurity.TransferScalarAdcShift01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarSbbPrimitive01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarAdcShift01 (sourceSplit128)
/-! Source-shaped util.rs SBB for reachable input borrow masks (zero/all ones).
The widening, wrapping subtraction, fixed high shift/casts yield the low limb
and exactly the next zero/all-ones borrow mask. Small constant-width arithmetic
lemmas isolate this primitive; no wide limb walk or runtime certification.
Rust primitive/trace and whole sub/add-back/byte layout remain interfaces. -/
def borrowMask (borrow : Bool) : UInt64 := if borrow then 0xffff_ffff_ffff_ffff else 0
def borrowBit (borrow : Bool) : Nat := if borrow then 1 else 0
def sbb128 (a b : UInt64) (borrow : Bool) : BitVec 128 :=
  BitVec.ofNat 128 a.toNat - (BitVec.ofNat 128 b.toNat + BitVec.ofNat 128 ((borrowMask borrow >>> 63).toNat))
def sbb64 (a b : UInt64) (borrow : Bool) : UInt64 × UInt64 := sourceSplit128 (sbb128 a b borrow)

theorem reachable_borrow_mask_high_bit_is_exact_boolean (borrow : Bool) :
    (borrowMask borrow >>> 63).toNat = borrowBit borrow := by
  cases borrow <;> decide

theorem widened_source_sbb_has_exact_wrapping_integer_form (a b : UInt64) (borrow : Bool) :
    (sbb128 a b borrow).toNat = ((2 ^ 128 - (b.toNat + borrowBit borrow)) + a.toNat) % 2 ^ 128 := by
  have bitBound : borrowBit borrow ≤ 1 := by cases borrow <;> decide
  have bitWide : borrowBit borrow < 2 ^ 128 := Nat.lt_of_le_of_lt bitBound (by decide)
  have aWide : a.toNat < 2 ^ 128 := Nat.lt_of_lt_of_le a.toNat_lt (by decide)
  have bWide : b.toNat < 2 ^ 128 := Nat.lt_of_lt_of_le b.toNat_lt (by decide)
  have sumWide : b.toNat + borrowBit borrow < 2 ^ 128 :=
    Nat.lt_of_le_of_lt (Nat.add_le_add (Nat.le_sub_one_of_lt b.toNat_lt) bitBound) (by decide)
  simp only [sbb128, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat,
    reachable_borrow_mask_high_bit_is_exact_boolean, Nat.mod_eq_of_lt aWide, Nat.mod_eq_of_lt bWide,
    Nat.mod_eq_of_lt bitWide, Nat.mod_eq_of_lt sumWide]

theorem nonunderflowing_sbb_returns_small_difference (a b : UInt64) (borrow : Bool)
    (enough : b.toNat + borrowBit borrow ≤ a.toNat) :
    (sbb128 a b borrow).toNat = a.toNat - (b.toNat + borrowBit borrow) := by
  rw [widened_source_sbb_has_exact_wrapping_integer_form]
  have aBound := a.toNat_lt
  have bBound := b.toNat_lt
  have bitBound : borrowBit borrow ≤ 1 := by cases borrow <;> decide
  omega

theorem underflowing_sbb_returns_exact_wrapped_difference (a b : UInt64) (borrow : Bool)
    (underflow : a.toNat < b.toNat + borrowBit borrow) :
    (sbb128 a b borrow).toNat = (2 ^ 128 - (b.toNat + borrowBit borrow)) + a.toNat := by
  rw [widened_source_sbb_has_exact_wrapping_integer_form]
  have aBound := a.toNat_lt
  have bBound := b.toNat_lt
  have bitBound : borrowBit borrow ≤ 1 := by cases borrow <;> decide
  omega

theorem source_sbb_low_word_and_next_borrow_mask_are_exact (a b : UInt64) (borrow : Bool) :
    (sbb64 a b borrow).2 = (if a.toNat < b.toNat + borrowBit borrow then borrowMask true else borrowMask false) ∧
    (sbb64 a b borrow).1.toNat + b.toNat + borrowBit borrow =
      a.toNat + radix64 * (if a.toNat < b.toNat + borrowBit borrow then 1 else 0) := by
  have aBound := a.toNat_lt
  have bBound := b.toNat_lt
  have bitBound : borrowBit borrow ≤ 1 := by cases borrow <;> decide
  unfold sbb64
  rw [TransferScalarAdcShift01.fixed_high_shift_and_cast_equals_radix_quotient_pair]
  unfold TransferScalarWordPrimitives01.split128
  by_cases underflow : a.toNat < b.toNat + borrowBit borrow
  · rw [if_pos underflow, underflowing_sbb_returns_exact_wrapped_difference a b borrow underflow]
    constructor
    · apply UInt64.toNat_inj.1
      change (((2 ^ 128 - (b.toNat + borrowBit borrow)) + a.toNat) / radix64) % 2 ^ 64 = 2 ^ 64 - 1
      unfold radix64
      omega
    · rw [if_pos underflow]
      change (((2 ^ 128 - (b.toNat + borrowBit borrow)) + a.toNat) % 2 ^ 64) + b.toNat + borrowBit borrow = a.toNat + radix64 * 1
      unfold radix64
      omega
  · have enough : b.toNat + borrowBit borrow ≤ a.toNat := Nat.le_of_not_gt underflow
    rw [if_neg underflow, nonunderflowing_sbb_returns_small_difference a b borrow enough]
    constructor
    · apply UInt64.toNat_inj.1
      change ((a.toNat - (b.toNat + borrowBit borrow)) / radix64) % 2 ^ 64 = 0
      unfold radix64
      omega
    · rw [if_neg underflow]
      change (a.toNat - (b.toNat + borrowBit borrow)) % 2 ^ 64 + b.toNat + borrowBit borrow = a.toNat + radix64 * 0
      unfold radix64
      omega

'''
names=['borrowMask','borrowBit','sbb128','sbb64','reachable_borrow_mask_high_bit_is_exact_boolean','widened_source_sbb_has_exact_wrapping_integer_form','nonunderflowing_sbb_returns_small_difference','underflowing_sbb_returns_exact_wrapped_difference','source_sbb_low_word_and_next_borrow_mask_are_exact']
for name in names:
    source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferScalarSbbPrimitive01\n'
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferScalarSbbPrimitive01.lean').write_text(source)
s=(DIAG/'transfer-scalar-adc-shift-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-scalar-four-round-wrapper-20261011-02'", "UPSTREAM = DIAG / 'transfer-scalar-adc-shift-20261011-02'")
replace("POOL = DIAG / 'transfer-scalar-adc-shift-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-scalar-sbb-primitive-owned-floor-20261011-02'")
replace("MODULE = 'TransferScalarAdcShift01'", "MODULE = 'TransferScalarSbbPrimitive01'")
s=s.replace("'runs/01-TransferScalarFourRoundWrapper01/stdout.txt'", "'runs/01-TransferScalarAdcShift01/stdout.txt'",1)
replace('assert len(current) == 14','assert len(current) == 8')
replace("records.append(('TransferScalarFourRoundWrapper01'", "records.append(('TransferScalarAdcShift01'")
replace("    'handwritten/TransferScalarFourRoundWrapper01.lean', 'project/ShielddSecurity/TransferScalarFourRoundWrapper01.lean']]", "    'handwritten/TransferScalarAdcShift01.lean', 'project/ShielddSecurity/TransferScalarAdcShift01.lean']]")
replace('assert len(records) == 82 and len(audits) == 777','assert len(records) == 83 and len(audits) == 785')
replace("'objects': 82", "'objects': 83")
s=s.replace('eighty-two-module','eighty-three-module').replace('777 inherited','785 inherited')
replace("'imports': ['ShielddSecurity.TransferScalarFourRoundWrapper01']", "'imports': ['ShielddSecurity.TransferScalarAdcShift01']")
replace('assert len(names) == 8','assert len(names) == 9')
replace("'fresh_audits': 8", "'fresh_audits': 9")
replace("[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', runner")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Source-shaped reachable-borrow-mask SBB widens finite UInt64 operands, extracts incoming mask high bit, uses BitVec128 wrapping subtraction and exact fixed shift/casts. Small lemmas prove full wrapping integer normal form, underflow/nonunderflow values, exact zero/all-ones outgoing borrow mask and low-word subtraction conservation. Nine full reports: four definitions/five theorems. Only single-word constant-width linear arithmetic, no wide constraint walk. Actual Rust primitive/trace/whole subtraction and add-back/endian semantics remain interfaces. Zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh reachable-mask single-word SBB arithmetic refinement on complete 785-report/83-module ancestry. Small finite-width lemmas, exact preserved source and diagnostics, no replay or guard changes.'"+s[end:]
s=s.replace('SOURCE_SCALAR_FIXED_HIGH_SHIFT_CAST_AND_ZERO_UPPER_ADC','SOURCE_SCALAR_REACHABLE_BORROW_MASK_SBB_SINGLE_WORD_ARITHMETIC')
s=s.replace('SCALAR_ADC_SHIFT_COMPLETE_EIGHTY_TWO_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SCALAR_SBB_PRIMITIVE_COMPLETE_EIGHTY_THREE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'inherited_audits': 777", "'inherited_audits': 785")

retained = "failedSbb = DIAG/'transfer-scalar-sbb-primitive-20261011-01'\nplan['pins'] += [pin(failedSbb/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarSbbPrimitive01.lean','project/ShielddSecurity/TransferScalarSbbPrimitive01.lean','runs/01-TransferScalarSbbPrimitive01/stdout.txt']]\n"
s=s.replace('unique = {}', retained+'unique = {}',1)
s=s.replace("[Path(__file__), ROOT / 'prepare_recipe.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner",1)
s=s.replace('Fresh reachable-mask single-word SBB arithmetic refinement', 'Fresh02 proof-only reduction of second branch conditional; all nine declarations unchanged, failed01 full raw diagnostics retained with zero credit. Fresh reachable-mask single-word SBB arithmetic refinement')

(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':9,'inherited_reports':785,'owned_modules':83,'native_correspondence_still_open':True})
