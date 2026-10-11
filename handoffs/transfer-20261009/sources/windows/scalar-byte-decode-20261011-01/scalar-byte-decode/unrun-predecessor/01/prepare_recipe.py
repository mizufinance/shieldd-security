"""Exact finite byte word decode and source-shaped canonical borrow predicate."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
library=DIAG/'transfer-bounded-native-codec-20261011-02/context/runtime-library/bls12_381-0.8.0-scalar.rs'
data=library.read_bytes();assert len(data)==36086 and hashlib.sha256(data).hexdigest()=='986f81e7fcb783a668bc4ab55721b22d497c5860cd7136e3cc600d2d9c321475'
text=data.decode();a=text.index('    pub fn from_bytes(bytes: &[u8; 32])');b=text.index('    /// Converts an element',a);body=text[a:b]
for i in range(4):
    assert f'tmp.0[{i}] = u64::from_le_bytes(<[u8; 8]>::try_from(&bytes[{8*i}..{8*(i+1)}]).unwrap());' in body
    assert f'sbb(tmp.0[{i}], MODULUS.0[{i}], '+('0' if i==0 else 'borrow')+');' in body
assert body.index('let is_some = (borrow as u8) & 1;')<body.index('tmp *= &R2;')<body.index('CtOption::new(tmp, Choice::from(is_some))')
(ROOT/'context').mkdir();shape={'library':{'path':str(library),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()},'shape':body,'scope':'Four finite LE word reads and four SBB canonical mask predicate; static exact library source association only. R2 multiplication and CtOption/Choice native semantics remain separate.'}
(ROOT/'context/decoder-shape.json').write_text(json.dumps(shape,indent=2,sort_keys=True)+'\n')
source='''import ShielddSecurity.TransferPartitionLocalRollback01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarByteDecode01
open TransferScalarLittleEndianBytes01 (decodeLE serializerBytes scalarKey)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarSerializationRange01 (radix64)
open TransferScalarFourRoundWrapper01 (modulusWords)
open TransferScalarBorrowWalk01 (borrowWalk)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Symbolic typed-byte decoder reads consecutive eight-byte LE words.
Full reconstruction and exact canonical borrow acceptance are derived,
including rejection of values at/above p; no byte-range or desired flag is
supplied. Native from_le_bytes/SBB/mask/Choice/CtOption/field representation,
R2 Montgomery conversion/compiler/full trace bindings remain explicit. -/

def decodeLEWords : Nat → List UInt8 → List UInt64
  | 0, _ => []
  | count + 1, bytes => UInt64.ofNat (decodeLE (bytes.take 8)) :: decodeLEWords count (bytes.drop 8)

theorem typed_byte_decode_is_below_positional_width (bytes : List UInt8) :
    decodeLE bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => decide
  | cons head rest ih =>
    have bounded : head.toNat < 256 := head.toNat_lt
    change head.toNat + 256 * decodeLE rest < 256 ^ (rest.length + 1)
    rw [Nat.pow_succ]
    omega

theorem decoded_word_list_has_exact_requested_width (count : Nat) (bytes : List UInt8) :
    (decodeLEWords count bytes).length = count := by
  induction count generalizing bytes with
  | zero => rfl
  | succ count ih =>
    change (decodeLEWords count (bytes.drop 8)).length + 1 = count + 1
    rw [ih]

theorem full_width_word_decoder_reconstructs_exact_little_endian_value
    (count : Nat) (bytes : List UInt8) (width : bytes.length = 8 * count) :
    packWords (decodeLEWords count bytes) = decodeLE bytes := by
  induction count generalizing bytes with
  | zero =>
    have empty : bytes = [] := List.eq_nil_of_length_eq_zero width
    subst bytes
    rfl
  | succ count ih =>
    have enough : 8 ≤ bytes.length := by omega
    have taken : (bytes.take 8).length = 8 := by rw [List.length_take, Nat.min_eq_left enough]
    have dropped : (bytes.drop 8).length = 8 * count := by rw [List.length_drop]; omega
    have bounded := typed_byte_decode_is_below_positional_width (bytes.take 8)
    rw [taken] at bounded
    have wordBound : decodeLE (bytes.take 8) < radix64 := bounded
    have joined := TransferScalarLittleEndianBytes01.little_endian_append_preserves_positional_value (bytes.take 8) (bytes.drop 8)
    rw [List.take_append_drop, taken] at joined
    change decodeLE (bytes.take 8) % radix64 + radix64 * packWords (decodeLEWords count (bytes.drop 8)) = decodeLE bytes
    rw [Nat.mod_eq_of_lt wordBound, ih _ dropped]
    exact joined.symm

def sourceCanonicalBorrowAccepts (bytes : Vector UInt8 32) : Bool :=
  (borrowWalk false ((decodeLEWords 4 bytes.toList).zip modulusWords)).2

theorem source_four_word_byte_decode_accepts_exact_canonical_integer (bytes : Vector UInt8 32) :
    sourceCanonicalBorrowAccepts bytes = true ↔ decodeLE bytes.toList < nullifierModulus := by
  have decodedWidth : (decodeLEWords 4 bytes.toList).length = 4 := decoded_word_list_has_exact_requested_width 4 bytes.toList
  have equalWidths : (decodeLEWords 4 bytes.toList).length = modulusWords.length :=
    decodedWidth.trans TransferScalarFourRoundWrapper01.modulus_words_have_four_limbs.symm
  change (borrowWalk false ((decodeLEWords 4 bytes.toList).zip modulusWords)).2 = true ↔ _
  rw [TransferScalarBorrowWalk01.final_borrow_is_exact_input_underflow,
    List.map_fst_zip (Nat.le_of_eq equalWidths), List.map_snd_zip (Nat.le_of_eq equalWidths.symm),
    TransferScalarFourRoundWrapper01.modulus_words_pack_to_actual_nullifier_modulus,
    full_width_word_decoder_reconstructs_exact_little_endian_value 4 bytes.toList Vector.length_toList]

theorem exact_source_serializer_bytes_pass_the_source_canonical_borrow_predicate
    (words : Vector UInt64 4) (bytes : Vector UInt8 32) (encoded : bytes.toList = serializerBytes words.toList) :
    sourceCanonicalBorrowAccepts bytes = true := by
  apply (source_four_word_byte_decode_accepts_exact_canonical_integer bytes).mpr
  rw [encoded]
  change scalarKey words < nullifierModulus
  exact TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_is_canonical words

'''
names=re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',source,re.M);assert len(names)==7
for name in names:source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferScalarByteDecode01\n'
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarByteDecode01.lean').write_text(source)
s=(DIAG/'transfer-partition-local-rollback-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-byte-key-cache-20261011-04'", "UPSTREAM = DIAG / 'transfer-partition-local-rollback-20261011-01'")
replace("POOL = DIAG / 'transfer-partition-local-rollback-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-scalar-byte-decode-owned-floor-20261011-01'")
replace("MODULE = 'TransferPartitionLocalRollback01'", "MODULE = 'TransferScalarByteDecode01'")
replace("stdout = UPSTREAM / 'runs/01-TransferByteKeyCache01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferPartitionLocalRollback01/stdout.txt'")
replace('assert len(current) == 7','assert len(current) == 4')
replace("records.append(('TransferByteKeyCache01'", "records.append(('TransferPartitionLocalRollback01'")
replace("    'handwritten/TransferByteKeyCache01.lean', 'project/ShielddSecurity/TransferByteKeyCache01.lean']]", "    'handwritten/TransferPartitionLocalRollback01.lean', 'project/ShielddSecurity/TransferPartitionLocalRollback01.lean']]")
replace('assert len(records) == 106 and len(audits) == 943','assert len(records) == 107 and len(audits) == 947')
replace("'objects': 106", "'objects': 107")
s=s.replace('one-hundred-six-module','one-hundred-seven-module').replace('943 inherited','947 inherited')
replace("'imports': ['ShielddSecurity.TransferByteKeyCache01']", "'imports': ['ShielddSecurity.TransferPartitionLocalRollback01']")
replace('assert len(names) == 4','assert len(names) == 7');replace("'fresh_audits': 4", "'fresh_audits': 7")
start=s.index('\nmapping = ');end=s.index("\nmapping['corrected_finalization_source_order']",start)
scope='Typed UInt8 eight-byte chunk decoder reconstructs exact raw integer into finite UInt64 limbs, with symbolic width/range derivation. Four-word source-shaped borrow predicate accepts iff exact32byte LE integer below p; every exact source serializer result passes. Seven full reports two definitions/five theorems. Native from_le_bytes/SBB/mask/Choice/CtOption/Scalar invariant, R2 Montgomery conversion/compiler/full trace binding remains explicit; zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}\nmapping['scalar_decode_source_shape']=pin(ROOT/'context/decoder-shape.json')"+s[end:]
a="plan['source_repairs'] = ";start=s.index(a);end=s.index('\n',start);s=s[:start]+a+repr(scope)+s[end:]
at=s.index("plan['artifact_policy']");s=s[:at]+"plan['pins'].append(mapping['scalar_decode_source_shape'])\n"+s[at:]
s=s.replace('PARTITION_LOCAL_ROLLBACK_COMPLETE_ONE_HUNDRED_SIX_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SCALAR_BYTE_DECODE_COMPLETE_ONE_HUNDRED_SEVEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN').replace("'inherited_audits': 943", "'inherited_audits': 947")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':7,'inherited_reports':947,'owned_modules':107,'montgomery_conversion_open':True})
