"""Generate read_record byte limit and source take/check model from exact pinned Rust."""
import ast, hashlib, json, re, sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
OUT=Path(sys.argv[1]).resolve() if len(sys.argv)==2 else ROOT
assert OUT.parent==DIAG and len(sys.argv)<=2
MODULE='TransferRecordReadBound01'
runtime=Path('C:/src/shieldd-pr160-844389ee/crates/core/component/sct/src/permanent_nullifiers/store.rs')
def pin(p):
    p=Path(p); b=p.read_bytes()
    return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
assert pin(runtime)['bytes']==32442 and pin(runtime)['sha256']=='434554cdb4bfb04f37a71707fb0c81ed77ffcf35677a5cab5aaaffd8832cb5a9'
text=runtime.read_text()
matches=re.findall(r'const MAX_RECORD_BYTES: u64 = ([0-9 *]+);',text); assert len(matches)==1
def arithmetic(node):
    if isinstance(node,ast.Constant) and type(node.value)==int and node.value>=0: return node.value
    if isinstance(node,ast.BinOp) and isinstance(node.op,ast.Mult): return arithmetic(node.left)*arithmetic(node.right)
    raise AssertionError('Unexpected source integer expression')
limit=arithmetic(ast.parse(matches[0],mode='eval').body); assert limit==4194304
body=text[text.index('fn read_record(file: File)'):text.index('fn sync_directory(path: &Path)')]
assert body.count('file.take(MAX_RECORD_BYTES + 1).read_to_end(&mut bytes)?;')==1
assert body.count('bytes.len() as u64 <= MAX_RECORD_BYTES')==1 and body.count('Ok(bytes)')==1
source='''import ShielddSecurity.TransferDurableWriteSource01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferRecordReadBound01
open TransferStateDelta (Bytes)
/-! Generated from the exact source MAX_RECORD_BYTES expression and source
read_record take/read_to_end/size-check flow. The callback supplies independently
observed returned bytes or read error. Native File/Take/Read semantics, partial
read errors, finite u8/usize/u64 embedding, allocation, ownership and OS state
remain explicit; modeled Nat length matches the source cast on native supported
32/64-bit word domains. No default record, serde validity, whole input consumption,
runtime negative control, native or full Transfer certification is inferred. -/
'''
source+='\ndef recordByteLimit : Nat := '+str(limit)+'\n'
source+=r'''
def sourceTakeLimit : Nat := recordByteLimit + 1

structure Io where
  readToEnd : Nat → Nat → Option Bytes

def readRecord (io : Io) (file : Nat) : Option Bytes :=
  (io.readToEnd file sourceTakeLimit).bind fun bytes =>
    if bytes.length ≤ recordByteLimit then some bytes else none

theorem source_take_limit_is_one_beyond_record_bound_and_fits_supported_words :
    sourceTakeLimit = recordByteLimit + 1 ∧ sourceTakeLimit < 2 ^ 32 ∧ sourceTakeLimit < 2 ^ 64 := by decide

theorem returned_record_derives_actual_bounded_read_bytes (io : Io) (file : Nat) (bytes : Bytes)
    (success : readRecord io file = some bytes) :
    io.readToEnd file sourceTakeLimit = some bytes ∧ bytes.length ≤ recordByteLimit := by
  cases read : io.readToEnd file sourceTakeLimit with
  | none => simp only [readRecord, read, Option.bind_none] at success; contradiction
  | some actual =>
    by_cases bounded : actual.length ≤ recordByteLimit
    · have same : actual = bytes := Option.some.inj (by simpa only [readRecord, read, Option.bind_some, if_pos bounded] using success)
      subst bytes
      exact ⟨rfl, bounded⟩
    · simp only [readRecord, read, Option.bind_some, if_neg bounded] at success
      cases success

theorem oversized_observed_record_refuses (io : Io) (file : Nat) (bytes : Bytes)
    (read : io.readToEnd file sourceTakeLimit = some bytes) (oversized : recordByteLimit < bytes.length) :
    readRecord io file = none := by
  simp only [readRecord, read, Option.bind_some, if_neg (Nat.not_le_of_gt oversized)]

theorem read_error_refuses_without_default (io : Io) (file : Nat)
    (failed : io.readToEnd file sourceTakeLimit = none) : readRecord io file = none := by
  simp only [readRecord, failed, Option.bind_none]
'''
names=['recordByteLimit','sourceTakeLimit','Io','readRecord',
 'source_take_limit_is_one_beyond_record_bound_and_fits_supported_words',
 'returned_record_derives_actual_bounded_read_bytes','oversized_observed_record_refuses','read_error_refuses_without_default']
for name in names:
    source+='\nset_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.'+MODULE+'\n'
p=OUT/'generated'/ (MODULE+'.lean'); assert not p.exists(); p.parent.mkdir(parents=True); p.write_text(source)
record={'module':MODULE,'source':pin(p),'runtime':pin(runtime),'generator':pin(__file__),'source_expression':matches[0],
 'record_byte_limit':limit,'fresh_audits':8,'native_credit':0,'certification':False}
manifest=OUT/'generation.json'; assert not manifest.exists()
manifest.write_bytes((json.dumps(record,indent=2,sort_keys=True)+'\n').encode())
print(json.dumps(record))
