"""Exact byte-key observation of symbolic cache writes, tombstones and overlays."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
source='''import ShielddSecurity.TransferScalarReversedByteOrder01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferByteKeyCache01
open TransferStateDelta
open TransferInjectiveKeyPublication01 (keyCode)
/-! Concrete byte-key observation map for the Nat-keyed cache model. The
proved global key encoding injection makes put/delete exact byte updates;
no-write, tombstone, overlay and latest-write merge are preserved. This is
an explicit semantic renaming relation rather than a hash identity argument.
Rust String/UTF8/hash-map/Clone/Any/ownership/trace binding stays separate. -/

def readAtBytes {V : Type} (view : View V) : Bytes → Option V :=
  fun key => view (keyCode key)

def writeAtBytes {V : Type} (writes : Writes V) : Bytes → Option (Option V) :=
  fun key => writes (keyCode key)

def putByteWrite {V : Type} (writes : Bytes → Option (Option V)) (key : Bytes) (value : Option V) :
    Bytes → Option (Option V) :=
  fun other => if other = key then some value else writes other

theorem encoded_key_equality_iff_exact_byte_key_equality (left right : Bytes) :
    keyCode left = keyCode right ↔ left = right :=
  ⟨TransferInjectiveKeyPublication01.keyCode_is_injective, congrArg keyCode⟩

theorem object_put_or_tombstone_is_exact_byte_key_update {O E : Type}
    (delta : Delta O E) (key : Bytes) (value : Option O) :
    writeAtBytes (putObject delta (keyCode key) value).cache.objects =
      putByteWrite (writeAtBytes delta.cache.objects) key value := by
  funext other
  simp only [writeAtBytes, putObject, putByteWrite, encoded_key_equality_iff_exact_byte_key_equality]

theorem byte_key_observation_preserves_overlay_no_write_and_tombstone {V : Type}
    (base : View V) (writes : Writes V) :
    readAtBytes (overlay base writes) =
      (fun key => match writeAtBytes writes key with
        | none => readAtBytes base key
        | some value => value) := rfl

theorem byte_key_observation_preserves_latest_write_merge {V : Type}
    (older newer : Writes V) :
    writeAtBytes (mergeWrites older newer) =
      (fun key => match writeAtBytes newer key with
        | none => writeAtBytes older key
        | some value => some value) := rfl

'''
names=re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',source,re.M);assert len(names)==7
for name in names:source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferByteKeyCache01\n'
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferByteKeyCache01.lean').write_text(source)
s=(DIAG/'transfer-scalar-reversed-byte-order-20261011-03/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-source-ordered-driver-20261011-01'", "UPSTREAM = DIAG / 'transfer-scalar-reversed-byte-order-20261011-03'")
replace("POOL = DIAG / 'transfer-scalar-reversed-byte-order-owned-floor-20261011-03'", "POOL = DIAG / 'transfer-byte-key-cache-owned-floor-20261011-01'")
replace("MODULE = 'TransferScalarReversedByteOrder01'", "MODULE = 'TransferByteKeyCache01'")
replace("stdout = UPSTREAM / 'runs/01-TransferSourceOrderedDriver01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferScalarReversedByteOrder01/stdout.txt'")
replace('assert len(current) == 4','assert len(current) == 8')
replace("records.append(('TransferSourceOrderedDriver01'", "records.append(('TransferScalarReversedByteOrder01'")
replace("    'handwritten/TransferSourceOrderedDriver01.lean', 'project/ShielddSecurity/TransferSourceOrderedDriver01.lean']]", "    'handwritten/TransferScalarReversedByteOrder01.lean', 'project/ShielddSecurity/TransferScalarReversedByteOrder01.lean']]")
replace('assert len(records) == 104 and len(audits) == 928','assert len(records) == 105 and len(audits) == 936')
replace("'objects': 104", "'objects': 105")
s=s.replace('one-hundred-four-module','one-hundred-five-module').replace('928 inherited','936 inherited')
replace("'imports': ['ShielddSecurity.TransferSourceOrderedDriver01','Init.Data.Nat.Compare']", "'imports': ['ShielddSecurity.TransferScalarReversedByteOrder01']")
replace('assert len(names) == 8','assert len(names) == 7');replace("'fresh_audits': 8", "'fresh_audits': 7")
replace("[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', runner")
start=s.index('\nmapping = ');end=s.index("\nmapping['corrected_finalization_source_order']",start)
scope='Concrete exact byte-key observation relation for Nat-keyed cache: proved globally injective keyCode labels make actual modeled object put/deletion tombstones exact byte-key updates. Overlay preserves no-write vs deletion, and merge preserves latest write. Seven complete reports three definitions/four theorems; semantic renaming rather than hash identity. Rust String/UTF8/hash-map/Any/Clone/ownership/compiler/cache/full trace binding remains explicit; zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
a="plan['source_repairs'] = ";start=s.index(a);end=s.index('\n',start);s=s[:start]+a+repr(scope)+s[end:]
s=s.replace('REVERSED_BYTE_ORDER_COMPLETE_ONE_HUNDRED_FOUR_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','BYTE_KEY_CACHE_COMPLETE_ONE_HUNDRED_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN').replace("'inherited_audits': 928", "'inherited_audits': 936")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':7,'inherited_reports':936,'owned_modules':105,'semantic_byte_key_relation':True})
