"""Install the fixed six known source mutations rather than a caller mutation list."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
context=json.loads((DIAG/'transfer-finalization-object-frames-20261011-01/context/known-finalization-object-mutators.json').read_bytes())
keys=[r['utf8'] for r in context['keys']]; assert len(keys)==6
tree=next(r for r in context['runtime_sources'] if r['path'].endswith('component\\tree.rs'))
manager=next(r for r in context['runtime_sources'] if r['path'].endswith('component\\manager.rs'))
texts={}
for row in [tree,manager]:
    data=Path(row['path']).read_bytes(); assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256'];texts[row['path']]=data.decode()
treeText=texts[tree['path']];managerText=texts[manager['path']]
a=treeText.index('    async fn end_sct_block(');b=treeText.index('    fn write_sct_cache(',a);sct=treeText[a:b]
assert sct.index('self.ensure_nullifier_block_sealed()?;')<sct.index('self.object_delete(state_key::cache::block_materialization());')<sct.index('self.write_sct(height, tree, block_root, epoch_root).await;')
a=treeText.index('    async fn write_sct(');b=treeText.index('    async fn prune_sct_history(',a);assert 'self.write_sct_cache(sct);' in treeText[a:b]
a=managerText.index('    async fn finalize_compact_block(');body=managerText[a:]
calls=['.end_sct_block(end_epoch)','self.pending_user_registrations()','self.pending_user_status_changes()','self.pending_asset_registrations()','self.object_delete(state_key::pending_routing_actions());']
positions=[body.index(c) for c in calls];assert positions==sorted(positions)
(ROOT/'context').mkdir()
shape={'runtime_sha':context['runtime_sha'],'known_mutation_order':context['keys'],'runtime_sources':[tree,manager],'call_positions':positions,'scope':'Known returned SCT/compact finishing path call ordering association only. Hidden callees/full App/component trace/native tree/value/Rust semantics and failures/panics remain separate; no exhaustive native trace or control credit.'}
(ROOT/'context/fixed-finalization-call-shape.json').write_text(json.dumps(shape,indent=2,sort_keys=True)+'\n')
oldSource=(DIAG/'transfer-injective-key-publication-20261011-02/handwritten/TransferInjectiveKeyPublication01.lean').read_text()
source=oldSource[:oldSource.index('/-!')]
source=source.replace('import ShielddSecurity.TransferInstalledSourcePublication01','import ShielddSecurity.TransferInjectiveKeyPublication01').replace('namespace ShielddSecurity.TransferInjectiveKeyPublication01','namespace ShielddSecurity.TransferFixedFinalizerPublication01')
source+='''open TransferInjectiveKeyPublication01 (keyCode)
open TransferFinalizationObjectFrames01 (Mutation)
/-! Fixed known post-seal object mutation recipe: delete block materialization,
replace cached tree with an actual native object, delete three compliance
buffers, then delete routing buffer. No caller mutation list/permitted-key
proof supplied. Source call ordering association is static, not an exhaustive
native trace refinement. Native component/hidden callee/tree/value/input/
codec/cache/ownership/OS correspondences remain distinct. -/

structure FinalizationWrites (O E A : Type) where
  nativeTreeObject : O
  verifiable : Writes Bytes
  nonverifiable : Writes Bytes
  events : List E
  queued : List A

def fixedMutations {O : Type} (nativeTreeObject : O) : List (Mutation (ExtendedObject O)) :=
  FIXED_MUTATION_LIST

def toEffects {O E A : Type} (writes : FinalizationWrites O E A) : Effects (ExtendedObject O) E A :=
  ⟨fixedMutations writes.nativeTreeObject, writes.verifiable, writes.nonverifiable, writes.events, writes.queued⟩

def installFixedIo {O E A : Type} (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (writesOf : Fin (2 ^ 64) → State (ExtendedObject O) → List A → FinalizationWrites O E A)
    (baseIo : TransferEndToEnd01.Io (ExtendedObject O) E A) : TransferEndToEnd01.Io (ExtendedObject O) E A :=
  installIo encodeNative decodeNative keyCode (fun height state queued => toEffects (writesOf height state queued)) baseIo

theorem fixed_mutation_recipe_has_exact_source_key_order {O : Type} (tree : O) :
    (fixedMutations tree).map (fun mutation => mutation.key) = FIXED_KEYS := rfl

theorem fixed_mutation_recipe_has_six_operations {O : Type} (tree : O) :
    (fixedMutations tree).length = 6 := rfl

theorem fixed_mutation_recipe_has_exact_put_and_deletion_tombstone_order {O : Type} (tree : O) :
    (fixedMutations tree).map (fun mutation => mutation.value.isSome) = [false, true, false, false, false, false] := rfl

'''
mutations=[]
for i,k in enumerate(keys):mutations.append('⟨'+repr(k)+', by decide, '+('some (.inl nativeTreeObject)' if i==1 else 'none')+'⟩')
source=source.replace('FIXED_MUTATION_LIST','['+',\n   '.join(mutations)+']').replace('FIXED_KEYS',repr(keys))
start=oldSource.index('theorem injective_labeled_source_and_finalizer_publish_exact_global_mathematical_input_vector');end=oldSource.index('\nset_option pp.all true in',start)
t=oldSource[start:end]
t=t.replace('injective_labeled_source_and_finalizer_publish_exact_global_mathematical_input_vector','fixed_known_source_finalization_publishes_exact_global_mathematical_input_vector',1)
a='(effectsOf : Fin (2 ^ 64) → State (ExtendedObject O) → List A → Effects (ExtendedObject O) E A)';assert t.count(a)==1
t=t.replace(a,'(writesOf : Fin (2 ^ 64) → State (ExtendedObject O) → List A → FinalizationWrites O E A)')
start=t.index(' := by\n');t=t[:start]+''' := by
  exact TransferInjectiveKeyPublication01.injective_labeled_source_and_finalizer_publish_exact_global_mathematical_input_vector
    encodeNative decodeNative supportedRoundtrip inputs wordOf sourceRequests parent queued final storedNativeDefault
    walkedNative (fun height state queued => toEffects (writesOf height state queued)) baseIo host height root currentState typedGetter success
'''
head,proof=t.split(' := by\n',1)
head=head.replace('installIo encodeNative decodeNative keyCode effectsOf baseIo','installFixedIo encodeNative decodeNative writesOf baseIo')
assert 'effectsOf' not in head
source+=head+' := by\n'+proof
names=re.findall(r'^(?:structure|def|theorem) ([A-Za-z0-9_]+)',source,re.M);assert len(names)==8
for name in names:source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferFixedFinalizerPublication01\n'
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferFixedFinalizerPublication01.lean').write_text(source)
s=(DIAG/'transfer-injective-key-publication-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-installed-source-publication-20261011-02'", "UPSTREAM = DIAG / 'transfer-injective-key-publication-20261011-02'")
replace("POOL = DIAG / 'transfer-injective-key-publication-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-fixed-finalizer-publication-owned-floor-20261011-01'")
replace("MODULE = 'TransferInjectiveKeyPublication01'", "MODULE = 'TransferFixedFinalizerPublication01'")
replace("stdout = UPSTREAM / 'runs/01-TransferInstalledSourcePublication01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferInjectiveKeyPublication01/stdout.txt'")
replace('assert len(current) == 7','assert len(current) == 6')
replace("records.append(('TransferInstalledSourcePublication01'", "records.append(('TransferInjectiveKeyPublication01'")
replace("    'handwritten/TransferInstalledSourcePublication01.lean', 'project/ShielddSecurity/TransferInstalledSourcePublication01.lean']]", "    'handwritten/TransferInjectiveKeyPublication01.lean', 'project/ShielddSecurity/TransferInjectiveKeyPublication01.lean']]")
replace('assert len(records) == 95 and len(audits) == 880','assert len(records) == 96 and len(audits) == 886')
replace("'objects': 95", "'objects': 96")
s=s.replace('ninety-five-module','ninety-six-module').replace('880 inherited','886 inherited')
replace("'imports': ['ShielddSecurity.TransferInstalledSourcePublication01']", "'imports': ['ShielddSecurity.TransferInjectiveKeyPublication01']")
replace('assert len(names) == 6','assert len(names) == 8');replace("'fresh_audits': 6", "'fresh_audits': 8")
replace("[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', runner")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Fixed six-key known post-seal source recipe constructs block-materialization deletion/cached tree replacement/three compliance buffer deletions/routing buffer deletion in exact source-associated order. Exact key order, operation count and put/deletion tombstone pattern proved. Installed whole pipeline derives exact source mathematical input vector/native sealed object/accepted inputs/application root/Ready writer/Idle Host/physical recovered boundary. Eight complete reports: one structure/three definitions/four theorems. No caller mutation list/permitted-key proofs/key-injectivity/source projection/canonical bounds/final field frame supplied. Native tree/hidden callees/full App trace completeness/order/value/input/codec/cache/ownership/OS bindings remain explicit. Known recipe only, not exhaustive native refinement. Zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
anchor="mapping_file = ROOT / 'source-mapping.json'";assert s.count(anchor)==1
s=s.replace(anchor,"mapping['fixed_finalization_source_association'] = pin(ROOT/'context/fixed-finalization-call-shape.json')\n"+anchor)
anchor="plan['pins'] += [mapping['action_projection_source_association'],mapping['known_finalization_source_association']]";assert s.count(anchor)==1
s=s.replace(anchor,anchor+"\nplan['pins'].append(mapping['fixed_finalization_source_association'])")
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
s=s.replace('INJECTIVE_KEY_PUBLICATION_COMPLETE_NINETY_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','FIXED_FINALIZER_PUBLICATION_COMPLETE_NINETY_SIX_MODULE_CLOSURE_SELF_REVIEWED_UNRUN').replace("'inherited_audits': 880", "'inherited_audits': 886")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':8,'inherited_reports':886,'owned_modules':96,'full_native_trace_still_open':True})
