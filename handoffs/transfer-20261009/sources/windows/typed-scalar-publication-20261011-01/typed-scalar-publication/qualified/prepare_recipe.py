"""Derive native input bounds and exact published values from typed scalar projection."""
import re
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
source='''import ShielddSecurity.TransferScalarMontgomeryValue01
import ShielddSecurity.TransferNativeOnlyPublication01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferTypedScalarPublication01
open TransferStateDelta
open TransferPendingFiniteCodec01 (NativePending restore)
open TransferBoundedNativeCodec01 (ExtendedObject encodeObject decodeObject nativeSupported nullifierModulus)
open TransferNullifierConsensusLimits01 (blockCapacity)
open TransferBlockPendingSequence01 (Request allInputs)
open TransferScalarLittleEndianBytes01 (scalarKey)
open TransferScalarMontgomeryValue01 (montgomeryValue)
/-! Typed four-word action inputs derive canonical range from the exact finite
source-shaped scalar serializer. The ordered whole-block source input vector
is exactly the mapped mathematical Montgomery values; ordinary native-only
pending/seal/publication preserves that same vector through accepted inputs,
application root and physical recovered boundary. No canonical input bound is
supplied. Actual action-to-typed-word source projection, Rust scalar/codec/
trace/Clone/field/ownership/snapshot/ICS23/OS bindings remain explicit;
this is conditional source-model composition, not native certification. -/

theorem typed_action_projection_derives_canonical_native_input_bounds {O E K X Tree A : Type}
    (requests : List (Request O E K X Tree A))
    (typedInputs : Request O E K X Tree A → List (Vector UInt64 4))
    (sourceProjection : ∀ request ∈ requests,
      request.config.inputs request.action = (typedInputs request).map scalarKey) :
    ∀ request ∈ requests, ∀ key ∈ request.config.inputs request.action, key < nullifierModulus := by
  intro request present key inside
  rw [sourceProjection request present] at inside
  obtain ⟨words, _, projected⟩ := List.mem_map.mp inside
  rw [← projected]
  exact TransferScalarLittleEndianBytes01.fixed_four_word_source_scalar_projection_is_canonical words

theorem global_source_input_vector_is_exact_typed_montgomery_projection {O E K X Tree A : Type}
    (requests : List (Request O E K X Tree A))
    (typedInputs : Request O E K X Tree A → List (Vector UInt64 4))
    (sourceProjection : ∀ request ∈ requests,
      request.config.inputs request.action = (typedInputs request).map scalarKey) :
    allInputs requests = (requests.flatMap typedInputs).map montgomeryValue := by
  induction requests with
  | nil => rfl
  | cons request rest ih =>
    change request.config.inputs request.action ++ allInputs rest =
      (typedInputs request ++ rest.flatMap typedInputs).map montgomeryValue
    rw [List.map_append, sourceProjection request List.mem_cons_self]
    have values : (typedInputs request).map scalarKey = (typedInputs request).map montgomeryValue :=
      List.map_congr_left (fun words _ =>
        TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value words)
    rw [values, ih (fun r inside => sourceProjection r (List.mem_cons_of_mem request inside))]

'''
old=(DIAG/'transfer-native-only-publication-20261011-01/handwritten/TransferNativeOnlyPublication01.lean').read_text()
start=old.index('theorem whole_native_only_default_block_publishes_exact_global_native_sealed_inputs')
end=old.index(' := by',start)
statement=old[start:end]
statement=statement.replace('whole_native_only_default_block_publishes_exact_global_native_sealed_inputs','whole_typed_scalar_default_block_publishes_exact_global_montgomery_values')
a='    (nativeInputs : ∀ request ∈ requests, ∀ key ∈ request.config.inputs request.action, key < nullifierModulus)'
assert statement.count(a)==1
statement=statement.replace(a,'''    (typedInputs : Request (ExtendedObject O) E K X Tree A → List (Vector UInt64 4))
    (sourceProjection : ∀ request ∈ requests,
      request.config.inputs request.action = (typedInputs request).map scalarKey)''')
a='    ∃ state,\n'
assert statement.count(a)==1
statement=statement.replace(a,'    allInputs requests = (requests.flatMap typedInputs).map montgomeryValue ∧\n    ∃ state,\n')
source+=statement+''' := by
  have nativeInputs := typed_action_projection_derives_canonical_native_input_bounds requests typedInputs sourceProjection
  exact ⟨global_source_input_vector_is_exact_typed_montgomery_projection requests typedInputs sourceProjection,
    TransferNativeOnlyPublication01.whole_native_only_default_block_publishes_exact_global_native_sealed_inputs
      encodeNative decodeNative supportedRoundtrip project injection requests parent queued final storedNativeDefault
      nativeInputs walkedNative io host height root currentState projectedKeys typedGetter finalization success⟩

'''
names=re.findall(r'^theorem ([A-Za-z0-9_]+)',source,re.M)
assert len(names)==3
for name in names:
    source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferTypedScalarPublication01\n'
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferTypedScalarPublication01.lean').write_text(source)
s=(DIAG/'transfer-scalar-montgomery-value-20261011-03/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-scalar-little-endian-bytes-20261011-02'", "UPSTREAM = DIAG / 'transfer-scalar-montgomery-value-20261011-03'")
replace("POOL = DIAG / 'transfer-scalar-montgomery-value-owned-floor-20261011-03'", "POOL = DIAG / 'transfer-typed-scalar-publication-owned-floor-20261011-01'")
replace("MODULE = 'TransferScalarMontgomeryValue01'", "MODULE = 'TransferTypedScalarPublication01'")
s=s.replace("'runs/01-TransferScalarLittleEndianBytes01/stdout.txt'", "'runs/01-TransferScalarMontgomeryValue01/stdout.txt'",1)
replace('assert len(current) == 15','assert len(current) == 13')
replace("records.append(('TransferScalarLittleEndianBytes01'", "records.append(('TransferScalarMontgomeryValue01'")
replace("    'handwritten/TransferScalarLittleEndianBytes01.lean', 'project/ShielddSecurity/TransferScalarLittleEndianBytes01.lean']]", "    'handwritten/TransferScalarMontgomeryValue01.lean', 'project/ShielddSecurity/TransferScalarMontgomeryValue01.lean']]")
replace('assert len(records) == 87 and len(audits) == 826','assert len(records) == 88 and len(audits) == 839')
replace("'objects': 87", "'objects': 88")
s=s.replace('eighty-seven-module','eighty-eight-module').replace('826 inherited','839 inherited')
replace("'imports': ['ShielddSecurity.TransferScalarLittleEndianBytes01']", "'imports': ['ShielddSecurity.TransferScalarMontgomeryValue01','ShielddSecurity.TransferNativeOnlyPublication01']")
replace('assert len(names) == 13','assert len(names) == 3')
replace("'fresh_audits': 13", "'fresh_audits': 3")
replace("[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', runner")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Typed finite four-word scalar action projection derives every native input key below nullifier modulus. Ordered global source inputs equal the actual typed scalar mathematical Montgomery projection, then exact native-only default walk/sealed object/accepted vector/application root/Ready writer/Idle Host/physical recovered boundary theorem composes without caller-supplied canonical range. Three complete theorem reports. Actual action-to-word projection and Rust scalar/codec/native trace/typed getter/finalization/field/library/snapshot/ICS23/ownership/OS interfaces remain explicit. Source-model composition only; zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh typed scalar exact publication join on exact 839-report/88-module qualified ancestry. Derived canonical range and exact ordered mathematical input vector from typed source projection; preserved source/diagnostic identities and all guards unchanged. No ancestor replay.'"+s[end:]
s=s.replace('SOURCE_SCALAR_EXACT_CANONICAL_MONTGOMERY_VALUE','SOURCE_TYPED_SCALAR_EXACT_PUBLICATION_JOIN')
s=s.replace('SCALAR_MONTGOMERY_VALUE_COMPLETE_EIGHTY_SEVEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','TYPED_SCALAR_PUBLICATION_COMPLETE_EIGHTY_EIGHT_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'inherited_audits': 826", "'inherited_audits': 839")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':3,'inherited_reports':839,'owned_modules':88,'native_correspondence_still_open':True})
