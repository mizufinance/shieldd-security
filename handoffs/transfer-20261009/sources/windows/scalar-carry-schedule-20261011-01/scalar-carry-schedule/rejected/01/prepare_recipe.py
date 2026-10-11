"""Prove symbolic finite MAC carry walk and low-limb quotient, not an unrolled constraint proof."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
source='''import ShielddSecurity.TransferScalarWordPrimitives01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarCarrySchedule01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords mac128 split128)
/-! Symbolic carry-chain conservation for the pinned scalar MAC schedule.
Each pair supplies the current accumulator limb and modulus limb. The exact
128-bit MAC feeds its carry into the next limb; the final carry is retained.
Dropping the low output limb and appending that carry gives integer division
by radix64. This closes the arithmetic schedule equation for arbitrary finite
vectors, without asserting Rust trace correspondence, ADC/SBB or byte layout. -/
def macLoop (multiplier carry : UInt64) : List (UInt64 × UInt64) → List UInt64 × UInt64
  | [] => ([], carry)
  | pair :: rest =>
    let step := split128 (mac128 pair.1 multiplier pair.2 carry)
    let after := macLoop multiplier step.2 rest
    (step.1 :: after.1, after.2)

def dropLowAndAppendCarry (output : List UInt64 × UInt64) : List UInt64 :=
  output.1.drop 1 ++ [output.2]

theorem packing_append_preserves_positional_value (left right : List UInt64) :
    packWords (left ++ right) = packWords left + radix64 ^ left.length * packWords right := by
  induction left with
  | nil => simp only [List.nil_append, packWords, List.length_nil, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
  | cons word rest ih =>
    change word.toNat + radix64 * packWords (rest ++ right) =
      (word.toNat + radix64 * packWords rest) + radix64 ^ (rest.length + 1) * packWords right
    rw [ih, Nat.pow_succ, Nat.mul_add]
    ac_rfl

theorem carry_walk_retains_limb_count (multiplier carry : UInt64) (pairs : List (UInt64 × UInt64)) :
    (macLoop multiplier carry pairs).1.length = pairs.length := by
  induction pairs generalizing carry with
  | nil => rfl
  | cons pair rest ih =>
    change (macLoop multiplier (split128 (mac128 pair.1 multiplier pair.2 carry)).2 rest).1.length + 1 = rest.length + 1
    rw [ih]

theorem carry_walk_conserves_full_integer (multiplier carry : UInt64) (pairs : List (UInt64 × UInt64)) :
    packWords (macLoop multiplier carry pairs).1 + radix64 ^ pairs.length * (macLoop multiplier carry pairs).2.toNat =
      packWords (pairs.map Prod.fst) + multiplier.toNat * packWords (pairs.map Prod.snd) + carry.toNat := by
  induction pairs generalizing carry with
  | nil => simp only [macLoop, packWords, List.map_nil, List.length_nil, Nat.pow_zero, Nat.one_mul, Nat.mul_zero, Nat.zero_add]
  | cons pair rest ih =>
    let step := split128 (mac128 pair.1 multiplier pair.2 carry)
    let after := macLoop multiplier step.2 rest
    have tail := ih step.2
    have first := TransferScalarWordPrimitives01.widened_u64_mac_low_word_and_carry_conserve_value pair.1 multiplier pair.2 carry
    change step.1.toNat + radix64 * packWords after.1 + radix64 ^ (rest.length + 1) * after.2.toNat =
      pair.1.toNat + radix64 * packWords (rest.map Prod.fst) +
        multiplier.toNat * (pair.2.toNat + radix64 * packWords (rest.map Prod.snd)) + carry.toNat
    calc
      _ = step.1.toNat + radix64 * (packWords after.1 + radix64 ^ rest.length * after.2.toNat) := by
        rw [Nat.pow_succ, Nat.mul_add]
        ac_rfl
      _ = step.1.toNat + radix64 * (packWords (rest.map Prod.fst) + multiplier.toNat * packWords (rest.map Prod.snd) + step.2.toNat) := by
        rw [tail]
      _ = (step.1.toNat + radix64 * step.2.toNat) + radix64 * packWords (rest.map Prod.fst) + multiplier.toNat * (radix64 * packWords (rest.map Prod.snd)) := by
        rw [Nat.mul_add, Nat.mul_add]
        ac_rfl
      _ = (pair.1.toNat + multiplier.toNat * pair.2.toNat + carry.toNat) + radix64 * packWords (rest.map Prod.fst) + multiplier.toNat * (radix64 * packWords (rest.map Prod.snd)) := by
        rw [first]
      _ = _ := by
        rw [Nat.mul_add]
        ac_rfl

theorem dropping_low_limb_and_appending_carry_is_radix_quotient
    (low carry : UInt64) (rest : List UInt64) :
    packWords (rest ++ [carry]) =
      (packWords (low :: rest) + radix64 ^ (rest.length + 1) * carry.toNat) / radix64 := by
  rw [packing_append_preserves_positional_value]
  change packWords rest + radix64 ^ rest.length * carry.toNat =
    (low.toNat + radix64 * packWords rest + radix64 ^ (rest.length + 1) * carry.toNat) / radix64
  symm
  calc
    _ = (low.toNat + radix64 * (packWords rest + radix64 ^ rest.length * carry.toNat)) / radix64 := by
      congr 1
      rw [Nat.pow_succ, Nat.mul_add]
      ac_rfl
    _ = low.toNat / radix64 + (packWords rest + radix64 ^ rest.length * carry.toNat) := Nat.add_mul_div_left _ _ (by decide)
    _ = _ := by rw [Nat.div_eq_of_lt low.toNat_lt, Nat.zero_add]

theorem nonempty_mac_walk_drops_to_exact_quotient
    (multiplier carry : UInt64) (pairs : List (UInt64 × UInt64)) (nonempty : pairs ≠ []) :
    packWords (dropLowAndAppendCarry (macLoop multiplier carry pairs)) =
      (packWords (pairs.map Prod.fst) + multiplier.toNat * packWords (pairs.map Prod.snd) + carry.toNat) / radix64 := by
  have conserved := carry_walk_conserves_full_integer multiplier carry pairs
  have length := carry_walk_retains_limb_count multiplier carry pairs
  cases output : (macLoop multiplier carry pairs).1 with
  | nil =>
    rw [output, List.length_nil] at length
    exact False.elim (nonempty (List.length_eq_zero.mp length.symm))
  | cons low rest =>
    change packWords ((macLoop multiplier carry pairs).1.drop 1 ++ [(macLoop multiplier carry pairs).2]) = _
    rw [output]
    change packWords (rest ++ [(macLoop multiplier carry pairs).2]) = _
    rw [output] at conserved length
    rw [← conserved, ← length]
    exact dropping_low_limb_and_appending_carry_is_radix_quotient low _ rest

'''
names=['macLoop','dropLowAndAppendCarry','packing_append_preserves_positional_value','carry_walk_retains_limb_count','carry_walk_conserves_full_integer','dropping_low_limb_and_appending_carry_is_radix_quotient','nonempty_mac_walk_drops_to_exact_quotient']
for name in names:
    source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferScalarCarrySchedule01\n'
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferScalarCarrySchedule01.lean').write_text(source)
s=(DIAG/'transfer-scalar-word-primitives-20261011-03/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-scalar-serialization-range-20261011-02'", "UPSTREAM = DIAG / 'transfer-scalar-word-primitives-20261011-03'")
replace("POOL = DIAG / 'transfer-scalar-word-primitives-owned-floor-20261011-03'", "POOL = DIAG / 'transfer-scalar-carry-schedule-owned-floor-20261011-01'")
replace("MODULE = 'TransferScalarWordPrimitives01'", "MODULE = 'TransferScalarCarrySchedule01'")
s=s.replace("'runs/01-TransferScalarSerializationRange01/stdout.txt'", "'runs/01-TransferScalarWordPrimitives01/stdout.txt'",1)
replace('assert len(current) == 8','assert len(current) == 10')
replace("records.append(('TransferScalarSerializationRange01'", "records.append(('TransferScalarWordPrimitives01'")
replace("    'handwritten/TransferScalarSerializationRange01.lean', 'project/ShielddSecurity/TransferScalarSerializationRange01.lean']]", "    'handwritten/TransferScalarWordPrimitives01.lean', 'project/ShielddSecurity/TransferScalarWordPrimitives01.lean']]")
replace('assert len(records) == 79 and len(audits) == 746','assert len(records) == 80 and len(audits) == 756')
replace("'objects': 79", "'objects': 80")
s=s.replace('seventy-nine-module','eighty-module').replace('746 inherited','756 inherited')
replace("'imports': ['ShielddSecurity.TransferScalarSerializationRange01','Init.Data.BitVec.Lemmas','Init.Data.UInt.Lemmas']", "'imports': ['ShielddSecurity.TransferScalarWordPrimitives01']")
replace('assert len(names) == 10','assert len(names) == 7')
replace("'fresh_audits': 10", "'fresh_audits': 7")
replace("[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', runner")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Symbolic finite MAC carry walk preserves limb count and full integer input+multiplier*modulus+initialCarry, using the exact widened UInt64 MAC arithmetic proof. Dropping the low output limb and appending the retained final carry equals division by radix64 for every nonempty pair vector. Seven full reports: two definitions/five theorems. No unrolled wide constraints. Source carry/loop shape association, actual Rust evaluation/ADC/SBB/four-round wrapper/byte layout correspondence remain separate. Zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh symbolic carry schedule and low-limb quotient proof on complete 756-report/80-module ancestry; all source identities and historical diagnostics retained, no replay or guard changes.'"+s[end:]
s=s.replace('SOURCE_SCALAR_FINITE_U64_INPUTS_AND_WIDENED_MAC_ARITHMETIC','SOURCE_SCALAR_SYMBOLIC_CARRY_SCHEDULE_AND_LOW_LIMB_QUOTIENT')
s=s.replace('SCALAR_WORD_PRIMITIVES_COMPLETE_SEVENTY_NINE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SCALAR_CARRY_SCHEDULE_COMPLETE_EIGHTY_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'inherited_audits': 746", "'inherited_audits': 756")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':7,'inherited_reports':756,'owned_modules':80,'native_correspondence_still_open':True})
