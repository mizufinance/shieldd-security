"""Derive actual sealed enum support from native-only walk and install finite native getter."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
oldSource=(DIAG/'transfer-fixed-finalizer-publication-20261011-01/handwritten/TransferFixedFinalizerPublication01.lean').read_text()
source=oldSource[:oldSource.index('/-!')]
source=source.replace('import ShielddSecurity.TransferInjectiveKeyPublication01','import ShielddSecurity.TransferFixedFinalizerPublication01').replace('namespace ShielddSecurity.TransferFixedFinalizerPublication01','namespace ShielddSecurity.TransferNativeGetterPublication01')
source+='''open TransferFixedFinalizerPublication01 (FinalizationWrites installFixedIo)
open TransferPendingSetInvariant01 (Invariant)
open TransferBoundedNativeCodec01 (BoundedPending)
open TransferBlockPendingSequence01 (parentPending)
/-! Successful default native-only walk derives global vector capacity/domain,
so the actual sealed enum is supported. Install the same finite native decoder
used by the walk as the publication getter and derive its exact reached enum
observation from the restricted supported native roundtrip. No caller reached
getter equality/capacity/domain supplied. Actual native codec/Clone/getter/
selectors/full trace/cache/ownership/OS correspondence remains explicit. -/

def installGetterIo {O E A : Type} (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (writesOf : Fin (2 ^ 64) → State (ExtendedObject O) → List A → FinalizationWrites O E A)
    (baseIo : TransferEndToEnd01.Io (ExtendedObject O) E A) : TransferEndToEnd01.Io (ExtendedObject O) E A :=
  installFixedIo encodeNative decodeNative writesOf
    {baseIo with ending := {baseIo.ending with decodePending := TransferPendingFiniteCodec01.decode (decodeObject decodeNative)}}

theorem native_default_walk_derives_supported_global_sealed_enum {O E K X Tree A : Type}
    (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (supportedRoundtrip : ∀ native, nativeSupported native = true → restore (decodeNative (encodeNative native)) = restore native)
    (project : Bytes → Nat) (injection : Function.Injective project)
    (requests : List (Request (ExtendedObject O) E K X Tree A))
    (parent : State (ExtendedObject O)) (queued : List A) (final : State (ExtendedObject O) × List A)
    (storedNativeDefault : parent.objects (project TransferNullifierObjectKeys01.nullifierBytes) =
      some (.inl (encodeNative (.opened [] []))))
    (nativeInputs : ∀ request ∈ requests, ∀ key ∈ request.config.inputs request.action, key < nullifierModulus)
    (walkedNative : TransferBlockPendingSequence01.walk (TransferNativeReachableErasure01.nativeOnlyEncode encodeNative)
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent queued requests = some final) :
    nativeSupported (.sealed (allInputs requests)) = true := by
'''
nativeOnly=(DIAG/'transfer-native-only-publication-20261011-01/handwritten/TransferNativeOnlyPublication01.lean').read_text()
start=nativeOnly.index('  have emptyBounded :');end=nativeOnly.index('\n  have nativeFinal :=',start)
source+=nativeOnly[start:end]+'\n'
source+='''  have order := TransferReachablePendingBlock01.empty_start_reachable_walk_derives_global_inputs
    (TransferPendingFiniteCodec01.encode (encodeObject encodeNative)) (TransferPendingFiniteCodec01.decode (decodeObject decodeNative))
    coherentRoundtrip0 project injection requests parent queued final emptyRead0 walked
  have bounds := TransferBoundedNativeCodec01.bounded_whole_input_vector_from_native_action_projections requests nativeInputs
  simp only [nativeSupported, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨order.2.2.2.1, bounds⟩

'''
start=oldSource.index('theorem fixed_known_source_finalization_publishes_exact_global_mathematical_input_vector');end=oldSource.index('\nset_option pp.all true in',start)
t=oldSource[start:end]
t=t.replace('fixed_known_source_finalization_publishes_exact_global_mathematical_input_vector','native_getter_source_finalization_publishes_exact_global_mathematical_input_vector',1)
start=t.index('    (typedGetter : ');end=t.index('    (success : ',start);t=t[:start]+t[end:]
start=t.index(' := by\n');t=t[:start]+''' := by
  let requests := installRequests inputs wordOf sourceRequests
  have sourceProjection := TransferInstalledSourcePublication01.installed_request_batch_derives_every_source_projection inputs wordOf sourceRequests
  have nativeInputs := TransferTypedScalarPublication01.typed_action_projection_derives_canonical_native_input_bounds
    requests (fun request => typedWords inputs wordOf request.action) sourceProjection
  have supported := native_default_walk_derives_supported_global_sealed_enum encodeNative decodeNative supportedRoundtrip
    keyCode TransferInjectiveKeyPublication01.keyCode_is_injective requests parent queued final storedNativeDefault nativeInputs walkedNative
  let getterBase : TransferEndToEnd01.Io (ExtendedObject O) E A :=
    {baseIo with ending := {baseIo.ending with decodePending := TransferPendingFiniteCodec01.decode (decodeObject decodeNative)}}
  have typedGetter : (installFixedIo encodeNative decodeNative writesOf getterBase).ending.decodePending
      (.inl (encodeNative (.sealed (allInputs requests)))) = restore (.sealed (allInputs requests)) := by
    change restore (decodeNative (encodeNative (.sealed (allInputs requests)))) = restore (.sealed (allInputs requests))
    exact supportedRoundtrip _ supported
  exact TransferFixedFinalizerPublication01.fixed_known_source_finalization_publishes_exact_global_mathematical_input_vector
    encodeNative decodeNative supportedRoundtrip inputs wordOf sourceRequests parent queued final storedNativeDefault
    walkedNative writesOf getterBase host height root currentState typedGetter success
'''
head,proof=t.split(' := by\n',1)
head=head.replace('installFixedIo encodeNative decodeNative writesOf baseIo','installGetterIo encodeNative decodeNative writesOf baseIo')
source+=head+' := by\n'+proof
names=re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',source,re.M);assert len(names)==3
for name in names:source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferNativeGetterPublication01\n'
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferNativeGetterPublication01.lean').write_text(source)
s=(DIAG/'transfer-fixed-finalizer-publication-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-injective-key-publication-20261011-02'", "UPSTREAM = DIAG / 'transfer-fixed-finalizer-publication-20261011-01'")
replace("POOL = DIAG / 'transfer-fixed-finalizer-publication-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-native-getter-publication-owned-floor-20261011-01'")
replace("MODULE = 'TransferFixedFinalizerPublication01'", "MODULE = 'TransferNativeGetterPublication01'")
replace("stdout = UPSTREAM / 'runs/01-TransferInjectiveKeyPublication01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferFixedFinalizerPublication01/stdout.txt'")
replace('assert len(current) == 6','assert len(current) == 8')
replace("records.append(('TransferInjectiveKeyPublication01'", "records.append(('TransferFixedFinalizerPublication01'")
replace("    'handwritten/TransferInjectiveKeyPublication01.lean', 'project/ShielddSecurity/TransferInjectiveKeyPublication01.lean']]", "    'handwritten/TransferFixedFinalizerPublication01.lean', 'project/ShielddSecurity/TransferFixedFinalizerPublication01.lean']]")
replace('assert len(records) == 96 and len(audits) == 886','assert len(records) == 97 and len(audits) == 894')
replace("'objects': 96", "'objects': 97")
s=s.replace('ninety-six-module','ninety-seven-module').replace('886 inherited','894 inherited')
replace("'imports': ['ShielddSecurity.TransferInjectiveKeyPublication01']", "'imports': ['ShielddSecurity.TransferFixedFinalizerPublication01']")
replace('assert len(names) == 8','assert len(names) == 3');replace("'fresh_audits': 8", "'fresh_audits': 3")
replace("pin(ROOT/'context/fixed-finalization-call-shape.json')", "pin(DIAG/'transfer-fixed-finalizer-publication-20261011-01/context/fixed-finalization-call-shape.json')")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Successful default native-only walk derives supported actual sealed global enum using capacity/domain already derived from installed source scalar inputs. Concrete publication getter installs the same finite native decoder as the walk; reached getter equality derives from restricted supported native roundtrip. Fixed six known source finalization mutations and proved key injection remain installed. Three complete reports: one definition/two theorems. No reached native getter equality/global capacity/domain/source projection/final field frame/key injection supplied to whole theorem. Restricted supported native roundtrip and native codec/Clone/getter/selector/full trace/cache/ownership/OS bindings remain explicit. Source model scope only; zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
s=s.replace('FIXED_FINALIZER_PUBLICATION_COMPLETE_NINETY_SIX_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','NATIVE_GETTER_PUBLICATION_COMPLETE_NINETY_SEVEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN').replace("'inherited_audits': 886", "'inherited_audits': 894")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':3,'inherited_reports':894,'owned_modules':97,'full_native_trace_still_open':True})
