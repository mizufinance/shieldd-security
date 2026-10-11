"""Exact source u64 borrow-mask to u8 low choice bit and canonical predicate."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
source='''import ShielddSecurity.TransferScalarByteDecode01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarChoiceBit01
open TransferScalarSbbPrimitive01 (borrowMask)
open TransferScalarByteDecode01 (sourceCanonicalBorrowAccepts)
open TransferScalarLittleEndianBytes01 (decodeLE serializerBytes)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Source-shaped low choice bit `(borrow as u8) & 1` follows the exact
zero/all-ones finite u64 mask. Derive both canonical success bit and refusal
bit from the parsed byte value, without supplying either flag. The model
does not claim actual CtOption/Choice construction or R2 payload conversion,
Scalar invariant/native primitive/compiler/full trace binding. -/

def borrowChoiceByte (borrow : Bool) : UInt8 :=
  UInt8.ofNat (borrowMask borrow).toNat &&& 1

theorem source_borrow_choice_byte_is_exact_zero_or_one (borrow : Bool) :
    borrowChoiceByte borrow = (if borrow then 1 else 0) := by
  cases borrow <;> decide

theorem source_borrow_choice_byte_is_one_exactly_on_underflow (borrow : Bool) :
    borrowChoiceByte borrow = 1 ↔ borrow = true := by
  cases borrow <;> decide

theorem source_borrow_choice_byte_is_zero_exactly_without_underflow (borrow : Bool) :
    borrowChoiceByte borrow = 0 ↔ borrow = false := by
  cases borrow <;> decide

def sourceCanonicalChoiceByte (bytes : Vector UInt8 32) : UInt8 :=
  borrowChoiceByte (sourceCanonicalBorrowAccepts bytes)

theorem source_canonical_choice_byte_is_one_iff_parsed_integer_below_modulus (bytes : Vector UInt8 32) :
    sourceCanonicalChoiceByte bytes = 1 ↔ decodeLE bytes.toList < nullifierModulus := by
  rw [sourceCanonicalChoiceByte, source_borrow_choice_byte_is_one_exactly_on_underflow,
    TransferScalarByteDecode01.source_four_word_byte_decode_accepts_exact_canonical_integer]

theorem source_canonical_choice_byte_is_zero_iff_parsed_integer_is_noncanonical (bytes : Vector UInt8 32) :
    sourceCanonicalChoiceByte bytes = 0 ↔ ¬ decodeLE bytes.toList < nullifierModulus := by
  rw [sourceCanonicalChoiceByte, source_borrow_choice_byte_is_zero_exactly_without_underflow]
  have accepted := TransferScalarByteDecode01.source_four_word_byte_decode_accepts_exact_canonical_integer bytes
  constructor
  · intro no less
    have yes := accepted.mpr less
    rw [no] at yes
    cases yes
  · intro noncanonical
    cases observed : sourceCanonicalBorrowAccepts bytes with
    | false => rfl
    | true => exact False.elim (noncanonical (accepted.mp observed))

theorem exact_source_serializer_bytes_derive_one_choice_byte
    (words : Vector UInt64 4) (bytes : Vector UInt8 32) (encoded : bytes.toList = serializerBytes words.toList) :
    sourceCanonicalChoiceByte bytes = 1 := by
  apply (source_canonical_choice_byte_is_one_iff_parsed_integer_below_modulus bytes).mpr
  exact (TransferScalarByteDecode01.source_four_word_byte_decode_accepts_exact_canonical_integer bytes).mp
    (TransferScalarByteDecode01.exact_source_serializer_bytes_pass_the_source_canonical_borrow_predicate words bytes encoded)

'''
names=re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',source,re.M);assert len(names)==8
for name in names:source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferScalarChoiceBit01\n'
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarChoiceBit01.lean').write_text(source)
s=(DIAG/'transfer-scalar-byte-decode-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-partition-local-rollback-20261011-01'", "UPSTREAM = DIAG / 'transfer-scalar-byte-decode-20261011-02'")
replace("POOL = DIAG / 'transfer-scalar-byte-decode-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-scalar-choice-bit-owned-floor-20261011-01'")
replace("MODULE = 'TransferScalarByteDecode01'", "MODULE = 'TransferScalarChoiceBit01'")
replace("stdout = UPSTREAM / 'runs/01-TransferPartitionLocalRollback01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferScalarByteDecode01/stdout.txt'")
replace('assert len(current) == 4','assert len(current) == 7')
replace("records.append(('TransferPartitionLocalRollback01'", "records.append(('TransferScalarByteDecode01'")
replace("    'handwritten/TransferPartitionLocalRollback01.lean', 'project/ShielddSecurity/TransferPartitionLocalRollback01.lean']]", "    'handwritten/TransferScalarByteDecode01.lean', 'project/ShielddSecurity/TransferScalarByteDecode01.lean']]")
replace('assert len(records) == 107 and len(audits) == 947','assert len(records) == 108 and len(audits) == 954')
replace("'objects': 107", "'objects': 108")
s=s.replace('one-hundred-seven-module','one-hundred-eight-module').replace('947 inherited','954 inherited')
replace("'imports': ['ShielddSecurity.TransferPartitionLocalRollback01']", "'imports': ['ShielddSecurity.TransferScalarByteDecode01']")
replace('assert len(names) == 7','assert len(names) == 8');replace("'fresh_audits': 7", "'fresh_audits': 8")
replace("[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', runner")
start=s.index('\nmapping = ');end=s.index("\nmapping['corrected_finalization_source_order']",start)
scope='Source-shaped UInt64 zero/all-ones borrow mask is cast to finite UInt8 and bitwise AND1; derived choice byte exactly0/1, one iff canonical parsed integer below p, zero iff noncanonical. Exact source serializer bytes derive one choice byte. Eight reports two definitions/six theorems, finite mask cases and symbolic decoded value, no desired flag supplied. Native Choice/CtOption/R2 payload conversion/Scalar invariant/primitive/compiler/full trace binding remains explicit; zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}\nmapping['scalar_decode_source_shape']=pin(DIAG/'transfer-scalar-byte-decode-20261011-02/context/decoder-shape.json')"+s[end:]
a="plan['source_repairs'] = ";start=s.index(a);end=s.index('\n',start);s=s[:start]+a+repr(scope)+s[end:]
s=s.replace('SCALAR_BYTE_DECODE_COMPLETE_ONE_HUNDRED_SEVEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SCALAR_CHOICE_BIT_COMPLETE_ONE_HUNDRED_EIGHT_MODULE_CLOSURE_SELF_REVIEWED_UNRUN').replace("'inherited_audits': 947", "'inherited_audits': 954")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':8,'inherited_reports':954,'owned_modules':108,'ctoption_payload_conversion_open':True})
