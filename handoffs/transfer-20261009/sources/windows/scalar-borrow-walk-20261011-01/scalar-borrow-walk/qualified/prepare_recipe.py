"""Symbolic finite SBB borrow recurrence; derive final underflow from actual output bound."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
source='''import ShielddSecurity.TransferScalarSbbPrimitive01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarBorrowWalk01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarSbbPrimitive01 (borrowMask borrowBit sbb64)
/-! Symbolic finite borrow walk over actual source-shaped SBB low limbs.
Each next Bool encodes the exact outgoing zero/all-ones source borrow mask,
proved from the primitive, and is fed into the next call. Conservation and
finite output bounds derive final underflow; no desired borrow outcome is
supplied. Rust trace, whole add-back and byte layout remain interfaces. -/
def nextBorrow (a b : UInt64) (borrow : Bool) : Bool :=
  if a.toNat < b.toNat + borrowBit borrow then true else false
def borrowWalk (borrow : Bool) : List (UInt64 × UInt64) → List UInt64 × Bool
  | [] => ([], borrow)
  | pair :: rest =>
    let step := sbb64 pair.1 pair.2 borrow
    let after := borrowWalk (nextBorrow pair.1 pair.2 borrow) rest
    (step.1 :: after.1, after.2)

theorem computed_next_borrow_encodes_actual_source_mask (a b : UInt64) (borrow : Bool) :
    (sbb64 a b borrow).2 = borrowMask (nextBorrow a b borrow) := by
  have exactMask := (TransferScalarSbbPrimitive01.source_sbb_low_word_and_next_borrow_mask_are_exact a b borrow).1
  by_cases underflow : a.toNat < b.toNat + borrowBit borrow
  · rw [nextBorrow, if_pos underflow]
    simpa only [if_pos underflow] using exactMask
  · rw [nextBorrow, if_neg underflow]
    simpa only [if_neg underflow] using exactMask

theorem computed_next_borrow_preserves_primitive_subtraction_equation (a b : UInt64) (borrow : Bool) :
    (sbb64 a b borrow).1.toNat + b.toNat + borrowBit borrow =
      a.toNat + radix64 * borrowBit (nextBorrow a b borrow) := by
  have conserved := (TransferScalarSbbPrimitive01.source_sbb_low_word_and_next_borrow_mask_are_exact a b borrow).2
  by_cases underflow : a.toNat < b.toNat + borrowBit borrow
  · rw [nextBorrow, if_pos underflow]
    simpa only [if_pos underflow] using conserved
  · rw [nextBorrow, if_neg underflow]
    simpa only [if_neg underflow] using conserved

theorem borrow_walk_retains_limb_count (borrow : Bool) (pairs : List (UInt64 × UInt64)) :
    (borrowWalk borrow pairs).1.length = pairs.length := by
  induction pairs generalizing borrow with
  | nil => rfl
  | cons pair rest ih =>
    change (borrowWalk (nextBorrow pair.1 pair.2 borrow) rest).1.length + 1 = rest.length + 1
    rw [ih]

theorem borrow_walk_conserves_full_subtraction_equation (borrow : Bool) (pairs : List (UInt64 × UInt64)) :
    packWords (borrowWalk borrow pairs).1 + packWords (pairs.map Prod.snd) + borrowBit borrow =
      packWords (pairs.map Prod.fst) + radix64 ^ pairs.length * borrowBit (borrowWalk borrow pairs).2 := by
  induction pairs generalizing borrow with
  | nil => simp [borrowWalk, packWords, borrowBit]
  | cons pair rest ih =>
    let next := nextBorrow pair.1 pair.2 borrow
    let step := sbb64 pair.1 pair.2 borrow
    let after := borrowWalk next rest
    have tail := ih next
    have first := computed_next_borrow_preserves_primitive_subtraction_equation pair.1 pair.2 borrow
    change (step.1.toNat + radix64 * packWords after.1) +
      (pair.2.toNat + radix64 * packWords (rest.map Prod.snd)) + borrowBit borrow =
      (pair.1.toNat + radix64 * packWords (rest.map Prod.fst)) +
        radix64 ^ (rest.length + 1) * borrowBit after.2
    calc
      _ = (step.1.toNat + pair.2.toNat + borrowBit borrow) + radix64 * packWords after.1 + radix64 * packWords (rest.map Prod.snd) := by ac_rfl
      _ = (pair.1.toNat + radix64 * borrowBit next) + radix64 * packWords after.1 + radix64 * packWords (rest.map Prod.snd) := by rw [first]
      _ = pair.1.toNat + radix64 * (packWords after.1 + packWords (rest.map Prod.snd) + borrowBit next) := by
        rw [Nat.mul_add, Nat.mul_add]
        ac_rfl
      _ = pair.1.toNat + radix64 * (packWords (rest.map Prod.fst) + radix64 ^ rest.length * borrowBit after.2) := by rw [tail]
      _ = _ := by
        rw [Nat.pow_succ, Nat.mul_add]
        ac_rfl

theorem final_borrow_is_exact_input_underflow (pairs : List (UInt64 × UInt64)) :
    (borrowWalk false pairs).2 = true ↔ packWords (pairs.map Prod.fst) < packWords (pairs.map Prod.snd) := by
  have conserved := borrow_walk_conserves_full_subtraction_equation false pairs
  have bounded := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power (borrowWalk false pairs).1
  rw [borrow_walk_retains_limb_count] at bounded
  cases final : (borrowWalk false pairs).2 with
  | false =>
    simp [borrowBit, final] at conserved
    constructor
    · intro impossible
      cases impossible
    · intro underflow
      omega
  | true =>
    simp [borrowBit, final] at conserved
    constructor
    · intro _
      omega
    · intro _
      rfl

'''
names=['nextBorrow','borrowWalk','computed_next_borrow_encodes_actual_source_mask','computed_next_borrow_preserves_primitive_subtraction_equation','borrow_walk_retains_limb_count','borrow_walk_conserves_full_subtraction_equation','final_borrow_is_exact_input_underflow']
for name in names:
    source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferScalarBorrowWalk01\n'
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferScalarBorrowWalk01.lean').write_text(source)
s=(DIAG/'transfer-scalar-sbb-primitive-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-scalar-adc-shift-20261011-02'", "UPSTREAM = DIAG / 'transfer-scalar-sbb-primitive-20261011-02'")
replace("POOL = DIAG / 'transfer-scalar-sbb-primitive-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-scalar-borrow-walk-owned-floor-20261011-01'")
replace("MODULE = 'TransferScalarSbbPrimitive01'", "MODULE = 'TransferScalarBorrowWalk01'")
s=s.replace("'runs/01-TransferScalarAdcShift01/stdout.txt'", "'runs/01-TransferScalarSbbPrimitive01/stdout.txt'",1)
replace('assert len(current) == 8','assert len(current) == 9')
replace("records.append(('TransferScalarAdcShift01'", "records.append(('TransferScalarSbbPrimitive01'")
replace("    'handwritten/TransferScalarAdcShift01.lean', 'project/ShielddSecurity/TransferScalarAdcShift01.lean']]", "    'handwritten/TransferScalarSbbPrimitive01.lean', 'project/ShielddSecurity/TransferScalarSbbPrimitive01.lean']]")
replace('assert len(records) == 83 and len(audits) == 785','assert len(records) == 84 and len(audits) == 794')
replace("'objects': 83", "'objects': 84")
s=s.replace('eighty-three-module','eighty-four-module').replace('785 inherited','794 inherited')
replace("'imports': ['ShielddSecurity.TransferScalarAdcShift01']", "'imports': ['ShielddSecurity.TransferScalarSbbPrimitive01']")
replace('assert len(names) == 9','assert len(names) == 7')
replace("'fresh_audits': 9", "'fresh_audits': 7")
replace("[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', runner")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Symbolic finite SBB borrow walk derives each next Boolean encoding from exact actual source-shaped outgoing zero/all-ones borrow mask, retains vector length and proves full multi-limb subtraction conservation. Finite output bounds derive final borrow iff packed input is smaller than packed subtrahend; no desired branch supplied. Seven full reports: two definitions/five theorems. Actual Rust primitive/trace/whole masked modulus add-back/endian correspondence remains separate. Zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh symbolic borrow schedule and derived exact final underflow on complete 794-report/84-module ancestry; small recurrences, no replay and all preserved source/diagnostic identities and guards unchanged.'"+s[end:]
s=s.replace('SOURCE_SCALAR_REACHABLE_BORROW_MASK_SBB_SINGLE_WORD_ARITHMETIC','SOURCE_SCALAR_SYMBOLIC_BORROW_WALK_AND_DERIVED_FINAL_UNDERFLOW')
s=s.replace('SCALAR_SBB_PRIMITIVE_COMPLETE_EIGHTY_THREE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SCALAR_BORROW_WALK_COMPLETE_EIGHTY_FOUR_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'inherited_audits': 785", "'inherited_audits': 794")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':7,'inherited_reports':794,'owned_modules':84,'native_correspondence_still_open':True})
