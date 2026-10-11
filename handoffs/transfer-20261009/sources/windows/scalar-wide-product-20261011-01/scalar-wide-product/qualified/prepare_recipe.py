"""Symbolic finite MAC schoolbook product, source16-call row association."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
library=DIAG/'transfer-bounded-native-codec-20261011-02/context/runtime-library/bls12_381-0.8.0-scalar.rs'
data=library.read_bytes();assert len(data)==36086 and hashlib.sha256(data).hexdigest()=='986f81e7fcb783a668bc4ab55721b22d497c5860cd7136e3cc600d2d9c321475'
text=data.decode();a=text.index('    pub const fn mul(&self, rhs: &Self)');b=text.index('    /// Subtracts',a);body=text[a:b]
rows=re.findall(r'let \((r\d), (carry|r\d)\) = mac\((0|r\d), self\.0\[(\d)\], rhs\.0\[(\d)\], (0|carry)\);',body)
expected=[(f'r{row+col}','carry' if col<3 else f'r{row+4}','0' if row==0 else f'r{row+col}',str(row),str(col),'0' if col==0 else 'carry') for row in range(4) for col in range(4)]
assert rows==expected and 'Scalar::montgomery_reduce(r0, r1, r2, r3, r4, r5, r6, r7)' in body
(ROOT/'context').mkdir();shape={'library':{'path':str(library),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()},'mac_rows':rows,'body':body,'scope':'Exact16 MAC call shapes, retained prefix and row carry; static source association only. Actual primitive evaluation, final wide Montgomery reduction and compiler binding separate.'}
(ROOT/'context/wide-product-shape.json').write_text(json.dumps(shape,indent=2,sort_keys=True)+'\n')
source='''import ShielddSecurity.TransferScalarChoiceBit01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarWideProduct01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarCarrySchedule01 (macLoop dropLowAndAppendCarry)
/-! Symbolic four-word schoolbook rows match source16 MAC call shape:
right/self selects each row multiplier, left/rhs supplies column words.
Retain one low word per row and carry into next four-word accumulator.
Full eight-limb integer product and range are derived without unrolled
wide constraint walks. Native primitive/compiler/source execution and final
wide Montgomery reduction remain explicit; no native/certification credit. -/

def multiplyWalk (left : List UInt64) : List UInt64 → List UInt64 → List UInt64
  | [], accumulated => accumulated
  | multiplier :: rest, accumulated =>
    let output := macLoop multiplier 0 (accumulated.zip left)
    output.1.headD 0 :: multiplyWalk left rest (dropLowAndAppendCarry output)

def sourceWideProduct (self rhs : Vector UInt64 4) : List UInt64 :=
  multiplyWalk rhs.toList self.toList (List.replicate 4 0)

theorem retained_low_word_and_shifted_carry_preserve_full_output
    (output : List UInt64 × UInt64) (nonempty : output.1 ≠ []) :
    (output.1.headD 0).toNat + radix64 * packWords (dropLowAndAppendCarry output) =
      packWords output.1 + radix64 ^ output.1.length * output.2.toNat := by
  cases output with
  | mk words carry =>
    cases words with
    | nil => exact False.elim (nonempty rfl)
    | cons low rest =>
      change low.toNat + radix64 * packWords (rest ++ [carry]) =
        low.toNat + radix64 * packWords rest + radix64 ^ (rest.length + 1) * carry.toNat
      rw [TransferScalarCarrySchedule01.packing_append_preserves_positional_value]
      change low.toNat + radix64 * (packWords rest + radix64 ^ rest.length * carry.toNat) = _
      rw [Nat.pow_succ, Nat.mul_add]
      ac_rfl

theorem four_word_mac_row_preserves_next_accumulator_width
    (multiplier : UInt64) (left accumulated : List UInt64)
    (leftWidth : left.length = 4) (accumulatedWidth : accumulated.length = 4) :
    (dropLowAndAppendCarry (macLoop multiplier 0 (accumulated.zip left))).length = 4 := by
  have length := TransferScalarCarrySchedule01.carry_walk_retains_limb_count multiplier 0 (accumulated.zip left)
  rw [List.length_zip, leftWidth, accumulatedWidth, Nat.min_self] at length
  change ((macLoop multiplier 0 (accumulated.zip left)).1.drop 1 ++
    [(macLoop multiplier 0 (accumulated.zip left)).2]).length = 4
  rw [List.length_append, List.length_drop, length]
  rfl

theorem finite_mac_row_derives_exact_accumulation_equation
    (multiplier : UInt64) (left accumulated : List UInt64)
    (leftWidth : left.length = 4) (accumulatedWidth : accumulated.length = 4) :
    ((macLoop multiplier 0 (accumulated.zip left)).1.headD 0).toNat +
      radix64 * packWords (dropLowAndAppendCarry (macLoop multiplier 0 (accumulated.zip left))) =
      packWords accumulated + multiplier.toNat * packWords left := by
  have equalWidths : accumulated.length = left.length := accumulatedWidth.trans leftWidth.symm
  have length := TransferScalarCarrySchedule01.carry_walk_retains_limb_count multiplier 0 (accumulated.zip left)
  rw [List.length_zip, leftWidth, accumulatedWidth, Nat.min_self] at length
  have nonempty : (macLoop multiplier 0 (accumulated.zip left)).1 ≠ [] := by
    intro empty
    rw [empty, List.length_nil] at length
    omega
  have retained := retained_low_word_and_shifted_carry_preserve_full_output (macLoop multiplier 0 (accumulated.zip left)) nonempty
  rw [length] at retained
  have conserved := TransferScalarCarrySchedule01.carry_walk_conserves_full_integer multiplier 0 (accumulated.zip left)
  rw [List.length_zip, leftWidth, accumulatedWidth, Nat.min_self,
    List.map_fst_zip (Nat.le_of_eq equalWidths), List.map_snd_zip (Nat.le_of_eq equalWidths.symm)] at conserved
  exact retained.trans conserved

theorem symbolic_schoolbook_walk_derives_width_and_exact_full_product
    (left right accumulated : List UInt64) (leftWidth : left.length = 4) (accumulatedWidth : accumulated.length = 4) :
    (multiplyWalk left right accumulated).length = 4 + right.length ∧
      packWords (multiplyWalk left right accumulated) = packWords accumulated + packWords right * packWords left := by
  induction right generalizing accumulated with
  | nil =>
    exact ⟨accumulatedWidth, by simp only [multiplyWalk, packWords, Nat.zero_mul, Nat.add_zero]⟩
  | cons multiplier rest ih =>
    let output := macLoop multiplier 0 (accumulated.zip left)
    have nextWidth := four_word_mac_row_preserves_next_accumulator_width multiplier left accumulated leftWidth accumulatedWidth
    have tail := ih (dropLowAndAppendCarry output) nextWidth
    have row := finite_mac_row_derives_exact_accumulation_equation multiplier left accumulated leftWidth accumulatedWidth
    constructor
    · change (multiplyWalk left rest (dropLowAndAppendCarry output)).length + 1 = 4 + (rest.length + 1)
      rw [tail.1]
      omega
    · change (output.1.headD 0).toNat + radix64 * packWords (multiplyWalk left rest (dropLowAndAppendCarry output)) =
        packWords accumulated + (multiplier.toNat + radix64 * packWords rest) * packWords left
      rw [tail.2, Nat.mul_add]
      calc
        _ = ((output.1.headD 0).toNat + radix64 * packWords (dropLowAndAppendCarry output)) +
            radix64 * (packWords rest * packWords left) := by ac_rfl
        _ = (packWords accumulated + multiplier.toNat * packWords left) +
            radix64 * (packWords rest * packWords left) := by rw [row]
        _ = _ := by rw [Nat.add_mul]; ac_rfl

theorem source_schoolbook_product_has_exact_eight_limbs_value_and_range (self rhs : Vector UInt64 4) :
    (sourceWideProduct self rhs).length = 8 ∧
      packWords (sourceWideProduct self rhs) = packWords self.toList * packWords rhs.toList ∧
      packWords (sourceWideProduct self rhs) < radix64 ^ 8 := by
  have full := symbolic_schoolbook_walk_derives_width_and_exact_full_product rhs.toList self.toList
    (List.replicate 4 0) Vector.length_toList (by decide)
  have width : (sourceWideProduct self rhs).length = 8 := by simpa only [sourceWideProduct, Vector.length_toList] using full.1
  have zero : packWords (List.replicate 4 (0 : UInt64)) = 0 := by decide
  have value : packWords (sourceWideProduct self rhs) = packWords self.toList * packWords rhs.toList := by
    simpa only [sourceWideProduct, zero, Nat.zero_add] using full.2
  have bounded := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power (sourceWideProduct self rhs)
  rw [width] at bounded
  exact ⟨width, value, bounded⟩

'''
names=re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',source,re.M);assert len(names)==7
for name in names:source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferScalarWideProduct01\n'
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarWideProduct01.lean').write_text(source)
s=(DIAG/'transfer-scalar-choice-bit-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-scalar-byte-decode-20261011-02'", "UPSTREAM = DIAG / 'transfer-scalar-choice-bit-20261011-01'")
replace("POOL = DIAG / 'transfer-scalar-choice-bit-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-scalar-wide-product-owned-floor-20261011-01'")
replace("MODULE = 'TransferScalarChoiceBit01'", "MODULE = 'TransferScalarWideProduct01'")
replace("stdout = UPSTREAM / 'runs/01-TransferScalarByteDecode01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferScalarChoiceBit01/stdout.txt'")
replace('assert len(current) == 7','assert len(current) == 8')
replace("records.append(('TransferScalarByteDecode01'", "records.append(('TransferScalarChoiceBit01'")
replace("    'handwritten/TransferScalarByteDecode01.lean', 'project/ShielddSecurity/TransferScalarByteDecode01.lean']]", "    'handwritten/TransferScalarChoiceBit01.lean', 'project/ShielddSecurity/TransferScalarChoiceBit01.lean']]")
replace('assert len(records) == 108 and len(audits) == 954','assert len(records) == 109 and len(audits) == 962')
replace("'objects': 108", "'objects': 109")
s=s.replace('one-hundred-eight-module','one-hundred-nine-module').replace('954 inherited','962 inherited')
replace("'imports': ['ShielddSecurity.TransferScalarByteDecode01']", "'imports': ['ShielddSecurity.TransferScalarChoiceBit01']")
replace('assert len(names) == 8','assert len(names) == 7');replace("'fresh_audits': 8", "'fresh_audits': 7")
start=s.index('\nmapping = ');end=s.index("\nmapping['corrected_finalization_source_order']",start)
scope='Source-shaped finite MAC schoolbook multiplication uses symbolic row recurrence, derives retained prefix/carry conservation, full eight-limb width, exact512bit packed integer product and bound for arbitrary typed four-word operands. Seven reports two definitions/five theorems; no unrolled wide constraint walk. Exact16 source MAC row-call association is static; native primitive/compiler/full execution and final wide Montgomery reduction binding remain explicit; zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}\nmapping['scalar_decode_source_shape']=pin(DIAG/'transfer-scalar-byte-decode-20261011-02/context/decoder-shape.json')\nmapping['wide_product_source_shape']=pin(ROOT/'context/wide-product-shape.json')"+s[end:]
a="plan['source_repairs'] = ";start=s.index(a);end=s.index('\n',start);s=s[:start]+a+repr(scope)+s[end:]
at=s.index("plan['artifact_policy']");s=s[:at]+"plan['pins'].append(mapping['wide_product_source_shape'])\n"+s[at:]
s=s.replace('SCALAR_CHOICE_BIT_COMPLETE_ONE_HUNDRED_EIGHT_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SCALAR_WIDE_PRODUCT_COMPLETE_ONE_HUNDRED_NINE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN').replace("'inherited_audits': 954", "'inherited_audits': 962")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':7,'inherited_reports':962,'owned_modules':109,'wide_montgomery_reduction_open':True})
