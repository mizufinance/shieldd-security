"""Derive publication pending frame from a concrete seal/object/V/NV finalizer."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
source='''import ShielddSecurity.TransferFinalizationObjectFrames01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferKnownFinalizerPublication01
open TransferStateDelta
open TransferPendingFiniteCodec01 (NativePending restore)
open TransferBoundedNativeCodec01 (ExtendedObject encodeObject decodeObject nativeSupported nullifierModulus)
open TransferNullifierConsensusLimits01 (blockCapacity)
open TransferBlockPendingSequence01 (Request allInputs)
open TransferScalarLittleEndianBytes01 (scalarKey)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferFinalizationObjectFrames01 (Mutation mutationWalk)
/-! Concrete source model finalizer seals, executes six-key object mutations,
overlays V/NV writes and returns observed queue/events. Installation derives
pending retention; publication no longer takes a desired pending field frame.
Effects may vary with actual height/sealed state/queue. Their allowed object
keys restrict this model to six known keys, not an exhaustive native trace.
Rust trace completeness/order/value/selector/codec/cache and every other native
correspondence remain separate; no native/control/certification credit. -/

structure Effects (O E A : Type) where
  mutations : List (Mutation O)
  verifiable : Writes Bytes
  nonverifiable : Writes Bytes
  events : List E
  queued : List A

def writeNonObjectEffects {O E A : Type} (delta : Delta O E) (effects : Effects O E A) : Delta O E :=
  {delta with cache := {delta.cache with verifiable := mergeWrites delta.cache.verifiable effects.verifiable,
    nonverifiable := mergeWrites delta.cache.nonverifiable effects.nonverifiable, events := delta.cache.events ++ effects.events}}

def finishKnown {O E A : Type} (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (project : Bytes → Nat)
    (effectsOf : Fin (2 ^ 64) → State (ExtendedObject O) → List A → Effects (ExtendedObject O) E A)
    (height : Fin (2 ^ 64)) (state : State (ExtendedObject O)) (queued : List A) :
    TransferHostEndBlock01.ApplicationResult (ExtendedObject O) E A :=
  let sealed := TransferGlobalCommitJoin01.sealedState (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
    (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project state
  let effects := effectsOf height sealed queued
  let after := writeNonObjectEffects (mutationWalk project ⟨sealed, (empty : Cache (ExtendedObject O) E)⟩ effects.mutations) effects
  ⟨applyCache after.parent after.cache, effects.queued, after.cache.events⟩

def installIo {O E A : Type} (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (project : Bytes → Nat)
    (effectsOf : Fin (2 ^ 64) → State (ExtendedObject O) → List A → Effects (ExtendedObject O) E A)
    (io : TransferEndToEnd01.Io (ExtendedObject O) E A) : TransferEndToEnd01.Io (ExtendedObject O) E A :=
  {io with ending := {io.ending with endApplication := finishKnown encodeNative decodeNative project effectsOf, project := project}}

theorem concrete_known_finalizer_derives_pending_retention {O E A : Type}
    (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (project : Bytes → Nat) (injection : Function.Injective project)
    (effectsOf : Fin (2 ^ 64) → State (ExtendedObject O) → List A → Effects (ExtendedObject O) E A)
    (height : Fin (2 ^ 64)) (state : State (ExtendedObject O)) (queued : List A) :
    (finishKnown encodeNative decodeNative project effectsOf height state queued).state.objects
      (project TransferNullifierObjectKeys01.nullifierBytes) =
      (TransferGlobalCommitJoin01.sealedState (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
        (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project state).objects
      (project TransferNullifierObjectKeys01.nullifierBytes) := by
  let sealed := TransferGlobalCommitJoin01.sealedState (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
    (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project state
  let effects := effectsOf height sealed queued
  change (applyCache (mutationWalk project ⟨sealed, (empty : Cache (ExtendedObject O) E)⟩ effects.mutations).parent
    (mutationWalk project ⟨sealed, (empty : Cache (ExtendedObject O) E)⟩ effects.mutations).cache).objects
      (project TransferNullifierObjectKeys01.nullifierBytes) = sealed.objects (project TransferNullifierObjectKeys01.nullifierBytes)
  exact TransferFinalizationObjectFrames01.symbolic_known_finalization_mutation_walk_preserves_pending_observation
    project injection ⟨sealed, (empty : Cache (ExtendedObject O) E)⟩ effects.mutations

theorem installed_known_finalizer_derives_reached_publication_field_frame {O E A : Type}
    (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (project : Bytes → Nat) (injection : Function.Injective project)
    (effectsOf : Fin (2 ^ 64) → State (ExtendedObject O) → List A → Effects (ExtendedObject O) E A)
    (io : TransferEndToEnd01.Io (ExtendedObject O) E A)
    (host : TransferHostSealedCommit01.Host (ExtendedObject O)) (height : Fin (2 ^ 64)) (queued : List A) :
    (TransferHostEndBlock01.finalized (installIo encodeNative decodeNative project effectsOf io).ending host height queued).state.objects
      (project TransferNullifierObjectKeys01.nullifierBytes) =
      (TransferGlobalCommitJoin01.sealedState (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
        (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project host.active).objects
      (project TransferNullifierObjectKeys01.nullifierBytes) :=
  concrete_known_finalizer_derives_pending_retention encodeNative decodeNative project injection effectsOf height host.active queued

'''
t=(DIAG/'transfer-typed-scalar-publication-20261011-01/handwritten/TransferTypedScalarPublication01.lean').read_text()
start=t.index('theorem whole_typed_scalar_default_block_publishes_exact_global_montgomery_values')
end=t.index('\nset_option pp.all true in',start)
t=t[start:end]
t=t.replace('whole_typed_scalar_default_block_publishes_exact_global_montgomery_values','concrete_known_finalizer_publishes_exact_global_typed_montgomery_values',1)
t=t.replace('(io : TransferEndToEnd01.Io (ExtendedObject O) E A)', '(effectsOf : Fin (2 ^ 64) → State (ExtendedObject O) → List A → Effects (ExtendedObject O) E A)\n    (baseIo : TransferEndToEnd01.Io (ExtendedObject O) E A)',1)
start=t.index('    (projectedKeys : ');end=t.index('    (typedGetter : ',start)
t=t[:start]+t[end:]
start=t.index('    (finalization : ');end=t.index('    (success : ',start)
t=t[:start]+t[end:]
start=t.index(' := by\n');t=t[:start]+''' := by
  let io := installIo encodeNative decodeNative project effectsOf baseIo
  exact TransferTypedScalarPublication01.whole_typed_scalar_default_block_publishes_exact_global_montgomery_values
    encodeNative decodeNative supportedRoundtrip project injection requests parent queued final storedNativeDefault
    typedInputs sourceProjection walkedNative io host height root currentState rfl typedGetter
    (installed_known_finalizer_derives_reached_publication_field_frame encodeNative decodeNative project injection effectsOf baseIo host height final.2)
    success
'''
head,proof=t.split(' := by\n',1)
head=re.sub(r'\bio\b', '(installIo encodeNative decodeNative project effectsOf baseIo)',head)
source+=head+' := by\n'+proof
names=re.findall(r'^(?:structure|def|theorem) ([A-Za-z0-9_]+)',source,re.M)
assert len(names)==7
for name in names: source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferKnownFinalizerPublication01\n'
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferKnownFinalizerPublication01.lean').write_text(source)
s=(DIAG/'transfer-finalization-object-frames-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-source-typed-input-projection-20261011-03'", "UPSTREAM = DIAG / 'transfer-finalization-object-frames-20261011-01'")
replace("POOL = DIAG / 'transfer-finalization-object-frames-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-known-finalizer-publication-owned-floor-20261011-01'")
replace("MODULE = 'TransferFinalizationObjectFrames01'", "MODULE = 'TransferKnownFinalizerPublication01'")
replace("'runs/01-TransferSourceTypedInputProjection01/stdout.txt'", "'runs/01-TransferFinalizationObjectFrames01/stdout.txt'")
replace('assert len(current) == 6','assert len(current) == 8')
replace("records.append(('TransferSourceTypedInputProjection01'", "records.append(('TransferFinalizationObjectFrames01'")
replace("    'handwritten/TransferSourceTypedInputProjection01.lean', 'project/ShielddSecurity/TransferSourceTypedInputProjection01.lean']]", "    'handwritten/TransferFinalizationObjectFrames01.lean', 'project/ShielddSecurity/TransferFinalizationObjectFrames01.lean']]")
replace('assert len(records) == 92 and len(audits) == 858','assert len(records) == 93 and len(audits) == 866')
replace("'objects': 92", "'objects': 93")
s=s.replace('ninety-two-module','ninety-three-module').replace('858 inherited','866 inherited')
replace("'imports': ['ShielddSecurity.TransferSourceTypedInputProjection01']", "'imports': ['ShielddSecurity.TransferFinalizationObjectFrames01']")
replace('assert len(names) == 8','assert len(names) == 7')
replace("'fresh_audits': 8", "'fresh_audits': 7")
replace("pin(ROOT/'context/known-finalization-object-mutators.json')", "pin(DIAG/'transfer-finalization-object-frames-20261011-01/context/known-finalization-object-mutators.json')")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Concrete source model finalizer seals, runs six-key object puts/deletion tombstones and V/NV overlays, and returns observed queue/events. Installed pipeline derives reached pending frame internally; exact global typed Montgomery vector, accepted inputs, application root, Ready writer, Idle Host and physical recovered boundary derive from ordinary success. Seven complete reports: one structure/three definitions/three theorems. No final pending-field frame or projected-key equality supplied. Typed action selectors/source projection and full Rust trace completeness/order/value/codec/cache/ownership/OS bindings remain explicit. Six known key trace scope, not exhaustive native finalization. Zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
s=s.replace('FINALIZATION_OBJECT_FRAMES_COMPLETE_NINETY_TWO_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','KNOWN_FINALIZER_PUBLICATION_COMPLETE_NINETY_THREE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'inherited_audits': 858", "'inherited_audits': 866")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':7,'inherited_reports':866,'owned_modules':93,'full_native_finalization_trace_still_open':True})
