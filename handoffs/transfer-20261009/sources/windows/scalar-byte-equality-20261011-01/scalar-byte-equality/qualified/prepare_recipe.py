"""Typed fixed-width byte equality exactly matches the source scalar modular value."""
import re
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
source='''import ShielddSecurity.TransferScalarPaddedCarry01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarByteEquality01
open TransferScalarLittleEndianBytes01 (decodeLE serializerBytes scalarKey)
open TransferScalarMontgomeryValue01 (montgomeryValue)
/-! Equality of exact finite source serializer byte keys and mathematical
Montgomery values. Typed UInt8 bounds derive exact head/remainder and
tail/quotient observations. A symbolic equal-width induction proves decoder
injectivity without a caller-provided byte-validity premise. The source
32-byte width and exact canonical projection then give equality equivalence.
Rust primitive/to_le_bytes/trace/type/library and native key correspondence
remain separate; no hash collision freedom or native control is claimed. -/

theorem typed_little_endian_head_is_exact_numeric_remainder (byte : UInt8) (rest : List UInt8) :
    decodeLE (byte :: rest) % 256 = byte.toNat := by
  change (byte.toNat + 256 * decodeLE rest) % 256 = byte.toNat
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt byte.toNat_lt

theorem typed_little_endian_tail_is_exact_numeric_quotient (byte : UInt8) (rest : List UInt8) :
    decodeLE (byte :: rest) / 256 = decodeLE rest := by
  have bounded : byte.toNat < 256 := byte.toNat_lt
  change (byte.toNat + 256 * decodeLE rest) / 256 = decodeLE rest
  rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt bounded, Nat.zero_add]

theorem typed_little_endian_decoder_is_injective_at_equal_width
    (left right : List UInt8) (width : left.length = right.length)
    (value : decodeLE left = decodeLE right) : left = right := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons byte rest => simp only [List.length_nil, List.length_cons] at width; omega
  | cons byte rest ih =>
    cases right with
    | nil => simp only [List.length_nil, List.length_cons] at width; omega
    | cons other tail =>
      have first := congrArg (fun n => n % 256) value
      change decodeLE (byte :: rest) % 256 = decodeLE (other :: tail) % 256 at first
      rw [typed_little_endian_head_is_exact_numeric_remainder,
        typed_little_endian_head_is_exact_numeric_remainder] at first
      have equalByte : byte = other := UInt8.toNat_inj.mp first
      have remaining := congrArg (fun n => n / 256) value
      change decodeLE (byte :: rest) / 256 = decodeLE (other :: tail) / 256 at remaining
      rw [typed_little_endian_tail_is_exact_numeric_quotient,
        typed_little_endian_tail_is_exact_numeric_quotient] at remaining
      have tailWidth : rest.length = tail.length := by
        simp only [List.length_cons] at width
        omega
      rw [equalByte, ih tail tailWidth remaining]

theorem source_scalar_typed_byte_keys_equal_iff_mathematical_montgomery_values_equal
    (left right : Vector UInt64 4) :
    serializerBytes left.toList = serializerBytes right.toList ↔
      montgomeryValue left = montgomeryValue right := by
  constructor
  · intro equalBytes
    have equalValue := congrArg decodeLE equalBytes
    change scalarKey left = scalarKey right at equalValue
    rw [TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value,
      TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value] at equalValue
    exact equalValue
  · intro equalValue
    apply typed_little_endian_decoder_is_injective_at_equal_width
    · rw [TransferScalarLittleEndianBytes01.source_scalar_serialization_has_exact_32_byte_width _ Vector.length_toList,
        TransferScalarLittleEndianBytes01.source_scalar_serialization_has_exact_32_byte_width _ Vector.length_toList]
    · change scalarKey left = scalarKey right
      rw [TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value,
        TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value]
      exact equalValue

'''
names=re.findall(r'^theorem ([A-Za-z0-9_]+)',source,re.M)
assert len(names)==4
for name in names:
    source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferScalarByteEquality01\n'
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferScalarByteEquality01.lean').write_text(source)
s=(DIAG/'transfer-scalar-padded-carry-20261011-03/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-typed-scalar-publication-20261011-01'", "UPSTREAM = DIAG / 'transfer-scalar-padded-carry-20261011-03'")
replace("POOL = DIAG / 'transfer-scalar-padded-carry-owned-floor-20261011-03'", "POOL = DIAG / 'transfer-scalar-byte-equality-owned-floor-20261011-01'")
replace("MODULE = 'TransferScalarPaddedCarry01'", "MODULE = 'TransferScalarByteEquality01'")
s=s.replace("'runs/01-TransferTypedScalarPublication01/stdout.txt'", "'runs/01-TransferScalarPaddedCarry01/stdout.txt'",1)
replace('assert len(current) == 3','assert len(current) == 6')
replace("records.append(('TransferTypedScalarPublication01'", "records.append(('TransferScalarPaddedCarry01'")
replace("    'handwritten/TransferTypedScalarPublication01.lean', 'project/ShielddSecurity/TransferTypedScalarPublication01.lean']]", "    'handwritten/TransferScalarPaddedCarry01.lean', 'project/ShielddSecurity/TransferScalarPaddedCarry01.lean']]")
replace('assert len(records) == 89 and len(audits) == 842','assert len(records) == 90 and len(audits) == 848')
replace("'objects': 89", "'objects': 90")
s=s.replace('eighty-nine-module','ninety-module').replace('842 inherited','848 inherited')
replace("'imports': ['ShielddSecurity.TransferTypedScalarPublication01','ShielddSecurity.TransferScalarAdcShift01','Init.Data.List.Nat.TakeDrop']", "'imports': ['ShielddSecurity.TransferScalarPaddedCarry01']")
replace('assert len(names) == 6','assert len(names) == 4')
replace("'fresh_audits': 6", "'fresh_audits': 4")
replace("[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', runner")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Finite UInt8 LE head/remainder and tail/quotient identities derive fixed equal-width decoder injectivity by symbolic list induction. Exact 32-byte source scalar serializer byte equality iff mathematical Montgomery value equality follows from actual typed source serializer projection. Four complete theorem reports. No caller-provided byte-validity premise or hash collision assumption; no wide constraint walk. Actual Rust to_le_bytes/primitive/native trace/type/library/key representation binding remains a separate correspondence obligation. Zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh finite byte key equality/value equivalence on exact 848-report/90-module qualified ancestry. Typed head/tail facts and small symbolic list induction; all guards unchanged and no ancestor replay.'"+s[end:]
s=s.replace('SOURCE_SCALAR_EXPLICIT_PADDED_MAC_ADC_CARRY_SCHEDULE','SOURCE_SCALAR_TYPED_BYTE_KEY_VALUE_EQUALITY')
s=s.replace('SCALAR_PADDED_CARRY_COMPLETE_EIGHTY_NINE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SCALAR_BYTE_EQUALITY_COMPLETE_NINETY_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'inherited_audits': 842", "'inherited_audits': 848")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':4,'inherited_reports':848,'owned_modules':90,'native_correspondence_still_open':True})
