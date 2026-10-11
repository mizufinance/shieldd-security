"""Known post-seal object writes/deletions preserve pending through typed finite key traces."""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
runtime=Path('C:/src/shieldd-pr160-844389ee')
def pin(p):
    p=Path(p);b=p.read_bytes()
    return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
keyPaths={
 'sct':runtime/'crates/core/component/sct/src/state_key.rs',
 'compact':runtime/'crates/core/component/compact-block/src/state_key.rs',
 'compliance':runtime/'crates/core/component/compliance/src/state_key.rs'}
descriptors=[('sct','block_materialization','delete'),('sct','cached_state_commitment_tree','put'),
 ('compact','pending_routing_actions','delete'),('compliance','pending_user_registrations','delete'),
 ('compliance','pending_user_status_changes','delete'),('compliance','pending_asset_registrations','delete')]
rows=[]
for provider,name,kind in descriptors:
    text=keyPaths[provider].read_text()
    expression=r'pub fn '+name+r'\(\) -> &\x27static str\s*\{\s*"([^"\n]+)"\s*\}'
    found=list(re.finditer(expression,text)); assert len(found)==1,(provider,name,len(found))
    match=found[0]; literal=match.group(1)
    rows.append({'provider':provider,'function':name,'operation':kind,'literal':literal,
      'utf8':list(literal.encode()),'key_source':pin(keyPaths[provider]),'line':text[:match.start()].count('\n')+1})
runtimeFiles=list(keyPaths.values())+[runtime/'crates/core/component/sct/src/component/tree.rs',
 runtime/'crates/core/component/compact-block/src/component/manager.rs',runtime/'crates/core/component/compliance/src/registry.rs']
tree=runtimeFiles[3].read_text();compact=runtimeFiles[4].read_text();registry=runtimeFiles[5].read_text()
assert tree.count('self.object_delete(state_key::cache::block_materialization());')==1
assert tree.count('self.object_put(state_key::cache::cached_state_commitment_tree(), tree);')==1
assert compact.count('self.object_delete(state_key::pending_routing_actions());')==1
for name in ['pending_user_registrations','pending_user_status_changes','pending_asset_registrations']:
    assert f'let key = state_key::{name}();' in registry
(ROOT/'context').mkdir()
(ROOT/'context/known-finalization-object-mutators.json').write_text(json.dumps({'kind':'KNOWN_SOURCE_POST_SEAL_OBJECT_PUT_DELETE_KEYS',
 'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a','keys':rows,'runtime_sources':[pin(p) for p in runtimeFiles],
 'scope':'Exact source literals and named mutator call shapes only. Six known SCT/compact/compliance object keys; not an exhaustive Rust trace proof. Finite mutation trace semantics use existing StateDelta tombstone-aware putObject. Completeness/order/value of native operation trace, every other component effect, Rust/Any/Clone/Arc/cache/OS semantics remain separate bindings. No proof/native/control/certification credit for JSON.'},indent=2,sort_keys=True)+'\n')
source='''import ShielddSecurity.TransferSourceTypedInputProjection01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferFinalizationObjectFrames01
open TransferStateDelta
open TransferNullifierObjectKeys01 (nullifierBytes)
open TransferBoundedNativeCodec01 (ExtendedObject)
open TransferPendingFiniteCodec01 (NativePending)
/-! Known post-seal object mutations include deletion tombstones as well as
SCT tree replacement. Exact pinned key literals are distinct from staged
nullifiers. A finite typed mutation trace invokes existing putObject and
derives pending-object preservation by symbolic induction. No desired final
pending field or per-step output frame is supplied. These cover the six named
SCT/compact/compliance keys only; completeness/order/value and execution of
the native full App finalization trace, all other component effects and
Rust/Any/Clone/Arc/cache/ownership/OS correspondence remain separate. -/

def otherKeys : List Bytes := KEY_BYTES_LITERAL

structure Mutation (O : Type) where
  key : Bytes
  permitted : key ∈ otherKeys
  value : Option O

def applyMutation {O E : Type} (project : Bytes → Nat) (delta : Delta O E) (mutation : Mutation O) : Delta O E :=
  putObject delta (project mutation.key) mutation.value

def mutationWalk {O E : Type} (project : Bytes → Nat) : Delta O E → List (Mutation O) → Delta O E
  | delta, [] => delta
  | delta, mutation :: rest => mutationWalk project (applyMutation project delta mutation) rest

theorem source_known_other_object_keys_are_all_separate_from_pending :
    otherKeys.all (fun key => decide (key ≠ nullifierBytes)) = true := by decide

theorem single_known_object_put_or_delete_preserves_pending_observation {O E : Type}
    (project : Bytes → Nat) (injection : Function.Injective project)
    (delta : Delta O E) (mutation : Mutation O) :
    (applyCache (applyMutation project delta mutation).parent (applyMutation project delta mutation).cache).objects
      (project nullifierBytes) = (applyCache delta.parent delta.cache).objects (project nullifierBytes) := by
  have allSeparate : ∀ key ∈ otherKeys, key ≠ nullifierBytes := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using source_known_other_object_keys_are_all_separate_from_pending
  have different : project nullifierBytes ≠ project mutation.key := by
    intro same
    exact allSeparate mutation.key mutation.permitted (injection same.symm)
  exact object_write_frames_other_key delta (project mutation.key) (project nullifierBytes) mutation.value different

theorem symbolic_known_finalization_mutation_walk_preserves_pending_observation {O E : Type}
    (project : Bytes → Nat) (injection : Function.Injective project)
    (delta : Delta O E) (mutations : List (Mutation O)) :
    (applyCache (mutationWalk project delta mutations).parent (mutationWalk project delta mutations).cache).objects
      (project nullifierBytes) = (applyCache delta.parent delta.cache).objects (project nullifierBytes) := by
  induction mutations generalizing delta with
  | nil => rfl
  | cons mutation rest ih =>
    exact (ih (applyMutation project delta mutation)).trans
      (single_known_object_put_or_delete_preserves_pending_observation project injection delta mutation)

theorem known_finalization_mutation_walk_retains_the_same_sealed_native_object {O E : Type}
    (project : Bytes → Nat) (injection : Function.Injective project)
    (encodeNative : NativePending → O) (inputs : List Nat)
    (delta : Delta (ExtendedObject O) E) (mutations : List (Mutation (ExtendedObject O)))
    (sealed : (applyCache delta.parent delta.cache).objects (project nullifierBytes) =
      some (.inl (encodeNative (.sealed inputs)))) :
    (applyCache (mutationWalk project delta mutations).parent (mutationWalk project delta mutations).cache).objects
      (project nullifierBytes) = some (.inl (encodeNative (.sealed inputs))) := by
  exact (symbolic_known_finalization_mutation_walk_preserves_pending_observation project injection delta mutations).trans sealed

'''.replace('KEY_BYTES_LITERAL',repr([r['utf8'] for r in rows]))
names=re.findall(r'^(?:structure|def|theorem) ([A-Za-z0-9_]+)',source,re.M)
assert len(names)==8
for name in names:
    source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferFinalizationObjectFrames01\n'
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferFinalizationObjectFrames01.lean').write_text(source)
s=(DIAG/'transfer-source-typed-input-projection-20261011-03/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-scalar-byte-equality-20261011-01'", "UPSTREAM = DIAG / 'transfer-source-typed-input-projection-20261011-03'")
replace("POOL = DIAG / 'transfer-source-typed-input-projection-owned-floor-20261011-03'", "POOL = DIAG / 'transfer-finalization-object-frames-owned-floor-20261011-01'")
replace("MODULE = 'TransferSourceTypedInputProjection01'", "MODULE = 'TransferFinalizationObjectFrames01'")
s=s.replace("'runs/01-TransferScalarByteEquality01/stdout.txt'", "'runs/01-TransferSourceTypedInputProjection01/stdout.txt'",1)
replace('assert len(current) == 4','assert len(current) == 6')
replace("records.append(('TransferScalarByteEquality01'", "records.append(('TransferSourceTypedInputProjection01'")
replace("    'handwritten/TransferScalarByteEquality01.lean', 'project/ShielddSecurity/TransferScalarByteEquality01.lean']]", "    'handwritten/TransferSourceTypedInputProjection01.lean', 'project/ShielddSecurity/TransferSourceTypedInputProjection01.lean']]")
replace('assert len(records) == 91 and len(audits) == 852','assert len(records) == 92 and len(audits) == 858')
replace("'objects': 91", "'objects': 92")
s=s.replace('ninety-one-module','ninety-two-module').replace('852 inherited','858 inherited')
replace("'imports': ['ShielddSecurity.TransferScalarByteEquality01']", "'imports': ['ShielddSecurity.TransferSourceTypedInputProjection01']")
replace('assert len(names) == 6','assert len(names) == 8')
replace("'fresh_audits': 6", "'fresh_audits': 8")
replace("[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', runner")
replace("pin(ROOT/'context/source-projection-shape.json')", "pin(DIAG/'transfer-source-typed-input-projection-20261011-03/context/source-projection-shape.json')")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Known post-seal SCT/compact/compliance object mutations include deletion tombstones and cached SCT tree replacement. Six exact source key literals are separate from pending-nullifier key; finite typed mutation trace uses original putObject and symbolic induction to derive unchanged pending observation and retention of the same already sealed native object. Eight complete reports: three definitions/one structure/four theorems. No desired final pending field or per-step output frame supplied. Named known mutators only: completeness/order/value/execution of the full native App trace and every other component effect/Rust/Any/Clone/Arc/cache/ownership/OS bindings remain explicit. Zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
anchor="mapping_file = ROOT / 'source-mapping.json'"
assert s.count(anchor)==1
s=s.replace(anchor,"mapping['known_finalization_source_association'] = pin(ROOT/'context/known-finalization-object-mutators.json')\nfinalizationAssociation = json.loads(Path(mapping['known_finalization_source_association']['path']).read_bytes())\nfor row in finalizationAssociation['runtime_sources']:\n    assert row['path'] not in runtime_rows or runtime_rows[row['path']] == row\n    runtime_rows[row['path']] = row\nmapping['runtime_sources'] = list(runtime_rows.values())\n"+anchor,1)
s=s.replace("plan['pins'] += [mapping['action_projection_source_association']]", "plan['pins'] += [mapping['action_projection_source_association'],mapping['known_finalization_source_association']]",1)
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh known finalization tombstone-aware object mutation trace on exact 858-report/92-module qualified ancestry. Source key separation and symbolic original putObject recurrence derive pending frame, not a supplied final object result. Scope restricted to six named keys; complete native App trace and all other effects remain interfaces. All guards unchanged, no ancestor replay.'"+s[end:]
s=s.replace('SOURCE_TRANSFER_CONCRETE_TYPED_INPUT_PROJECTION','SOURCE_KNOWN_POST_SEAL_OBJECT_MUTATION_FRAMES')
s=s.replace('SOURCE_TYPED_INPUT_PROJECTION_COMPLETE_NINETY_ONE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','FINALIZATION_OBJECT_FRAMES_COMPLETE_NINETY_TWO_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'inherited_audits': 852", "'inherited_audits': 858")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':8,'inherited_reports':858,'owned_modules':92,'full_native_finalization_trace_still_open':True})
