"""Install exact all-slot source requests and derive both source and finalizer frames."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
source='''import ShielddSecurity.TransferKnownFinalizerPublication01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferInstalledSourcePublication01
open TransferStateDelta
open TransferPendingFiniteCodec01 (NativePending restore)
open TransferBoundedNativeCodec01 (ExtendedObject encodeObject decodeObject nativeSupported nullifierModulus)
open TransferNullifierConsensusLimits01 (blockCapacity)
open TransferBlockPendingSequence01 (Request allInputs)
open TransferScalarLittleEndianBytes01 (scalarKey)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferSourceTypedInputProjection01 (typedWords installTypedInputs)
open TransferKnownFinalizerPublication01 (Effects installIo)
/-! Concrete typed source request construction preserves every actual input
slot/order and derives the configuration projection. Native input selectors
and source nonemptiness are explicit. Whole publication supplies neither
desired source-key equality, canonical bounds, nor finalization field frame.
Full native input/Scalar/iterator/proof/codec/six-key trace completeness/cache/
ownership/OS correspondences remain separate. Source-model composition only. -/

structure SourceRequest (O E K X Tree A I : Type) (inputs : A → List I) where
  base : Request O E K X Tree A
  sourceNonempty : (inputs base.action).isEmpty = false

def installRequest {O E K X Tree A I : Type} (inputs : A → List I) (wordOf : I → Vector UInt64 4)
    (request : SourceRequest O E K X Tree A I inputs) : Request O E K X Tree A :=
  {request.base with config := installTypedInputs request.base.config inputs wordOf, supported := request.base.supported, nonempty := by
    change ((inputs request.base.action).map (fun input => scalarKey (wordOf input))).isEmpty = false
    rw [List.isEmpty_map]
    exact request.sourceNonempty}

def installRequests {O E K X Tree A I : Type} (inputs : A → List I) (wordOf : I → Vector UInt64 4)
    (requests : List (SourceRequest O E K X Tree A I inputs)) : List (Request O E K X Tree A) :=
  requests.map (installRequest inputs wordOf)

theorem installed_request_derives_exact_typed_input_projection {O E K X Tree A I : Type}
    (inputs : A → List I) (wordOf : I → Vector UInt64 4) (request : SourceRequest O E K X Tree A I inputs) :
    (installRequest inputs wordOf request).config.inputs (installRequest inputs wordOf request).action =
      (typedWords inputs wordOf (installRequest inputs wordOf request).action).map scalarKey :=
  TransferSourceTypedInputProjection01.installed_config_inputs_are_exact_ordered_typed_scalar_projection
    request.base.config inputs wordOf request.base.action

theorem installed_request_batch_derives_every_source_projection {O E K X Tree A I : Type}
    (inputs : A → List I) (wordOf : I → Vector UInt64 4) (requests : List (SourceRequest O E K X Tree A I inputs)) :
    ∀ request ∈ installRequests inputs wordOf requests,
      request.config.inputs request.action = (typedWords inputs wordOf request.action).map scalarKey := by
  intro request present
  obtain ⟨original, _, same⟩ := List.mem_map.mp present
  subst request
  exact installed_request_derives_exact_typed_input_projection inputs wordOf original

theorem installed_request_batch_retains_exact_ordered_source_word_vector {O E K X Tree A I : Type}
    (inputs : A → List I) (wordOf : I → Vector UInt64 4) (requests : List (SourceRequest O E K X Tree A I inputs)) :
    (installRequests inputs wordOf requests).flatMap (fun request => typedWords inputs wordOf request.action) =
      requests.flatMap (fun request => typedWords inputs wordOf request.base.action) := by
  change (requests.map (installRequest inputs wordOf)).flatMap (fun request => typedWords inputs wordOf request.action) = _
  rw [List.flatMap_map]
  rfl

'''
t=(DIAG/'transfer-known-finalizer-publication-20261011-03/handwritten/TransferKnownFinalizerPublication01.lean').read_text()
start=t.index('theorem concrete_known_finalizer_publishes_exact_global_typed_montgomery_values');end=t.index('\nset_option pp.all true in',start)
t=t[start:end]
t=t.replace('concrete_known_finalizer_publishes_exact_global_typed_montgomery_values','installed_source_and_finalizer_publish_exact_global_mathematical_input_vector',1)
t=t.replace('{O E K X Tree A : Type}','{O E K X Tree A I : Type}',1)
t=t.replace('(requests : List (Request (ExtendedObject O) E K X Tree A))','(inputs : A → List I) (wordOf : I → Vector UInt64 4)\n    (sourceRequests : List (SourceRequest (ExtendedObject O) E K X Tree A I inputs))',1)
start=t.index('    (typedInputs : ');end=t.index('    (walkedNative : ',start)
t=t[:start]+t[end:]
start=t.index(' := by\n');t=t[:start]+''' := by
  let requests := installRequests inputs wordOf sourceRequests
  obtain ⟨values, publication⟩ := TransferKnownFinalizerPublication01.concrete_known_finalizer_publishes_exact_global_typed_montgomery_values
    encodeNative decodeNative supportedRoundtrip project injection requests parent queued final storedNativeDefault
    (fun request => typedWords inputs wordOf request.action)
    (installed_request_batch_derives_every_source_projection inputs wordOf sourceRequests)
    walkedNative effectsOf baseIo host height root currentState typedGetter success
  refine ⟨values.trans ?_, publication⟩
  exact congrArg (fun words : List (Vector UInt64 4) => words.map montgomeryValue)
    (installed_request_batch_retains_exact_ordered_source_word_vector inputs wordOf sourceRequests)
'''
head,proof=t.split(' := by\n',1)
head=head.replace('(requests.flatMap typedInputs)', '(sourceRequests.flatMap (fun request => typedWords inputs wordOf request.base.action))')
head=re.sub(r'\brequests\b','(installRequests inputs wordOf sourceRequests)',head)
source+=head+' := by\n'+proof
names=re.findall(r'^(?:structure|def|theorem) ([A-Za-z0-9_]+)',source,re.M)
assert len(names)==7
for name in names: source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferInstalledSourcePublication01\n'
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferInstalledSourcePublication01.lean').write_text(source)
s=(DIAG/'transfer-known-finalizer-publication-20261011-03/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-finalization-object-frames-20261011-01'", "UPSTREAM = DIAG / 'transfer-known-finalizer-publication-20261011-03'")
replace("POOL = DIAG / 'transfer-known-finalizer-publication-owned-floor-20261011-03'", "POOL = DIAG / 'transfer-installed-source-publication-owned-floor-20261011-01'")
replace("MODULE = 'TransferKnownFinalizerPublication01'", "MODULE = 'TransferInstalledSourcePublication01'")
replace("stdout = UPSTREAM / 'runs/01-TransferFinalizationObjectFrames01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferKnownFinalizerPublication01/stdout.txt'")
replace('assert len(current) == 8','assert len(current) == 7')
replace("records.append(('TransferFinalizationObjectFrames01'", "records.append(('TransferKnownFinalizerPublication01'")
replace("    'handwritten/TransferFinalizationObjectFrames01.lean', 'project/ShielddSecurity/TransferFinalizationObjectFrames01.lean']]", "    'handwritten/TransferKnownFinalizerPublication01.lean', 'project/ShielddSecurity/TransferKnownFinalizerPublication01.lean']]")
replace('assert len(records) == 93 and len(audits) == 866','assert len(records) == 94 and len(audits) == 873')
replace("'objects': 93", "'objects': 94")
s=s.replace('ninety-three-module','ninety-four-module').replace('866 inherited','873 inherited')
replace("'imports': ['ShielddSecurity.TransferFinalizationObjectFrames01']", "'imports': ['ShielddSecurity.TransferKnownFinalizerPublication01']")
replace("[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', runner")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Concrete typed source request installation preserves all input slots/order and derives every configuration source projection. Concrete known six-key finalizer derives retained pending field internally. Ordinary success derives exact source ordered mathematical Montgomery vector, sealed native object, canonical bounds/Nodup/capacity, accepted inputs/application root/Ready writer/Idle Host/physical recovered boundary. Seven complete reports: one structure/two definitions/four theorems. No source-key equality/canonical bounds/finalization field frame/projected-key equality premise supplied. Actual input/word selectors/source nonemptiness, native full trace completeness/order/value/proof/codec/cache/ownership/OS bindings remain explicit. Source model scope, no native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
s=s.replace('KNOWN_FINALIZER_PUBLICATION_COMPLETE_NINETY_THREE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','INSTALLED_SOURCE_PUBLICATION_COMPLETE_NINETY_FOUR_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'inherited_audits': 866", "'inherited_audits': 873")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':7,'inherited_reports':873,'owned_modules':94,'full_native_trace_still_open':True})
