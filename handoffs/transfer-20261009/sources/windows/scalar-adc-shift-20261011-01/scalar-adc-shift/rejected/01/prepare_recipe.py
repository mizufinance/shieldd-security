"""Prove pinned fixed-shift casts and zero-upper ADC match retained finite carry."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
source='''import ShielddSecurity.TransferScalarFourRoundWrapper01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarAdcShift01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (mac128 split128)
/-! Model of the pinned util.rs fixed 64-bit shift/casts and widened ADC.
The shift pair equals the proved quotient pair. ADC is a unit-multiplier MAC,
so its low/high words conserve the full sum. For the serializer's zero high
word and zero carry2, ADC retains the MAC carry with no overflow. These close
arithmetic model equations; Rust primitive/trace and SBB/endian remain separate. -/
def sourceSplit128 (ret : BitVec 128) : UInt64 × UInt64 :=
  (UInt64.ofNat ret.toNat, UInt64.ofNat ((ret >>> 64).toNat))
def adc128 (a b carry : UInt64) : BitVec 128 :=
  BitVec.ofNat 128 a.toNat + BitVec.ofNat 128 b.toNat + BitVec.ofNat 128 carry.toNat
def adc64 (a b carry : UInt64) : UInt64 × UInt64 := sourceSplit128 (adc128 a b carry)

theorem fixed_high_shift_and_cast_equals_radix_quotient_pair (ret : BitVec 128) :
    sourceSplit128 ret = split128 ret := by
  unfold sourceSplit128 split128
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem widened_adc_is_unit_multiplier_mac (a b carry : UInt64) :
    adc128 a b carry = mac128 a 1 b carry := by
  change BitVec.ofNat 128 a.toNat + BitVec.ofNat 128 b.toNat + BitVec.ofNat 128 carry.toNat =
    BitVec.ofNat 128 a.toNat + (1 : BitVec 128) * BitVec.ofNat 128 b.toNat + BitVec.ofNat 128 carry.toNat
  rw [BitVec.one_mul]

theorem widened_adc_preserves_full_integer_sum (a b carry : UInt64) :
    (adc128 a b carry).toNat = a.toNat + b.toNat + carry.toNat := by
  rw [widened_adc_is_unit_multiplier_mac, TransferScalarWordPrimitives01.widened_u64_mac_preserves_full_integer,
    UInt64.toNat_one, Nat.one_mul]

theorem widened_adc_low_word_and_carry_conserve_sum (a b carry : UInt64) :
    (adc64 a b carry).1.toNat + radix64 * (adc64 a b carry).2.toNat = a.toNat + b.toNat + carry.toNat := by
  unfold adc64
  rw [fixed_high_shift_and_cast_equals_radix_quotient_pair,
    TransferScalarWordPrimitives01.split_double_word_preserves_full_integer, widened_adc_preserves_full_integer_sum]

theorem zero_upper_limb_adc_retains_carry_without_overflow (carry : UInt64) :
    adc64 0 0 carry = (carry, 0) := by
  unfold adc64
  rw [fixed_high_shift_and_cast_equals_radix_quotient_pair]
  unfold split128
  rw [widened_adc_preserves_full_integer_sum, UInt64.toNat_zero, Nat.zero_add]
  have bounded : carry.toNat < radix64 := carry.toNat_lt
  rw [UInt64.ofNat_toNat, Nat.div_eq_of_lt bounded]
  rfl

'''
names=['sourceSplit128','adc128','adc64','fixed_high_shift_and_cast_equals_radix_quotient_pair','widened_adc_is_unit_multiplier_mac','widened_adc_preserves_full_integer_sum','widened_adc_low_word_and_carry_conserve_sum','zero_upper_limb_adc_retains_carry_without_overflow']
for name in names:
    source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferScalarAdcShift01\n'
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferScalarAdcShift01.lean').write_text(source)
s=(DIAG/'transfer-scalar-four-round-wrapper-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-scalar-carry-schedule-20261011-02'", "UPSTREAM = DIAG / 'transfer-scalar-four-round-wrapper-20261011-02'")
replace("POOL = DIAG / 'transfer-scalar-four-round-wrapper-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-scalar-adc-shift-owned-floor-20261011-01'")
replace("MODULE = 'TransferScalarFourRoundWrapper01'", "MODULE = 'TransferScalarAdcShift01'")
s=s.replace("'runs/01-TransferScalarCarrySchedule01/stdout.txt'", "'runs/01-TransferScalarFourRoundWrapper01/stdout.txt'",1)
replace('assert len(current) == 7','assert len(current) == 14')
replace("records.append(('TransferScalarCarrySchedule01'", "records.append(('TransferScalarFourRoundWrapper01'")
replace("    'handwritten/TransferScalarCarrySchedule01.lean', 'project/ShielddSecurity/TransferScalarCarrySchedule01.lean']]", "    'handwritten/TransferScalarFourRoundWrapper01.lean', 'project/ShielddSecurity/TransferScalarFourRoundWrapper01.lean']]")
replace('assert len(records) == 81 and len(audits) == 763','assert len(records) == 82 and len(audits) == 777')
replace("'objects': 81", "'objects': 82")
s=s.replace('eighty-one-module','eighty-two-module').replace('763 inherited','777 inherited')
replace("'imports': ['ShielddSecurity.TransferScalarCarrySchedule01','Init.Data.List.Zip']", "'imports': ['ShielddSecurity.TransferScalarFourRoundWrapper01']")
replace('assert len(names) == 14','assert len(names) == 8')
replace("'fresh_audits': 14", "'fresh_audits': 8")
replace("[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', runner")
replace("pin(ROOT/'context/source-association.json')", "pin(DIAG/'transfer-scalar-four-round-wrapper-20261011-02/context/source-association.json')")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Fixed BitVec128 right shift by64 then UInt64 cast equals the proven radix quotient pair. Widened ADC equals unit-multiplier MAC and conserves the full sum. The zero-upper-limb/zero-carry2 serializer ADC retains the finite carry and produces zero overflow, supporting carry appending in the four-round model. Eight full reports: three definitions/five theorems. Exact pinned util source association inherited; Rust primitive evaluation/native schedule/sub/byte trace correspondence remains separate. Zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh fixed-shift/cast and widened ADC equations close zero-high serializer carry model obligation; complete 777-report/82-module qualified ancestry reused without replay, historical diagnostics and all guards unchanged.'"+s[end:]
s=s.replace('SOURCE_SCALAR_FOUR_ROUND_FINITE_CARRY_WRAPPER_CANONICAL_RANGE','SOURCE_SCALAR_FIXED_HIGH_SHIFT_CAST_AND_ZERO_UPPER_ADC')
s=s.replace('SCALAR_FOUR_ROUND_WRAPPER_COMPLETE_EIGHTY_ONE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SCALAR_ADC_SHIFT_COMPLETE_EIGHTY_TWO_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'inherited_audits': 763", "'inherited_audits': 777")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':8,'inherited_reports':777,'owned_modules':82,'native_correspondence_still_open':True})
