"""Generate the exact runtime object-key join; never patch generated Lean."""
import hashlib, json, re, sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
OUT=Path(sys.argv[1]).resolve() if len(sys.argv)==2 else ROOT
assert OUT.parent==DIAG and len(sys.argv)<=2
MODULE='TransferNullifierObjectKeys01'
RUNTIME=Path('C:/src/shieldd-pr160-844389ee')
def pin(p):
    p=Path(p); b=p.read_bytes()
    return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
files={
 'sct':(RUNTIME/'crates/core/component/sct/src/state_key.rs',2762,'abe8ace0f7498431b9d1cb3a17655527f1a6fb905bbf1b0e1ba10c03e406b14d'),
 'pool':(RUNTIME/'crates/core/component/shielded-pool/src/state_key.rs',1484,'754918fa1a1192751e95efdcda1055d25c3583d87d0c2040b83ffaf1600aded5')}
for p,size,sha in files.values():
    row=pin(p); assert row['bytes']==size and row['sha256']==sha
source=DIAG/'transfer-pending-nullifier-retention-20261011-02/handwritten/TransferPendingNullifierRetention01.lean'
assert pin(source)['bytes']==23787 and pin(source)['sha256']=='6667bf22971da3ef1d916ae210ec695bd191b2efc4d507641dfdac4868596326'
entries=[('nullifierBytes','sct','pending_block'),('treeBytes','sct','cached_state_commitment_tree'),
         ('notesBytes','pool','pending_notes'),('volumeBytes','pool','pending_volume_accumulator_payloads')]
literals={}
for name,owner,function in entries:
    text=files[owner][0].read_text()
    matches=re.findall(r'pub fn '+function+r'\(\)\s*->\s*&\x27static str\s*\{\s*"([^"\n]+)"\s*\}',text)
    assert len(matches)==1
    literals[name]=matches[0]
    literals[name].encode('ascii')
upstream=source.read_text()
signature=upstream[upstream.index('theorem whole_delivery_success_retains_bounded_fresh_pending_nullifier_encoding'):]
signature=signature.split(' := by',1)[0]
signature=signature.replace('whole_delivery_success_retains_bounded_fresh_pending_nullifier_encoding','whole_success_retains_source_key_pending_nullifier_encoding')
old='    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)'
assert signature.count(old)==1
signature=signature.replace(old,'    (project : Bytes → Nat) (injection : Function.Injective project)\n    (wordMax capacity payload entryKey dayKey : Nat)')
old='    (notTree : nullifierKey ≠ treeKey) (notNotes : nullifierKey ≠ notesKey) (notVolume : nullifierKey ≠ volumeKey)\n'
assert signature.count(old)==1
signature=signature.replace(old,'')
for old,new in [('treeKey','(project treeBytes)'),('notesKey','(project notesBytes)'),('volumeKey','(project volumeBytes)'),('nullifierKey','(project nullifierBytes)')]:
    signature=re.sub(r'\b'+old+r'\b',new,signature)
lean='''import ShielddSecurity.TransferPendingNullifierRetention01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace ShielddSecurity.TransferNullifierObjectKeys01
open TransferStateDelta TransferRawStateProgram01 TransferIndexWriterModel01
open TransferVerificationEqualitySource01 (Item)
/-! Generated only from exact pinned Rust static object-key literals and the
qualified whole retained-pending theorem. Byte inequality and an explicit
injective representation projection discharge all three key inequalities.
Hashing supplies source identity, not Rust semantics or cryptographic truth.
Native object/getter/codec/ownership/tree/reader/token/durability stay open. -/
'''
for name in literals:
    lean+='\ndef '+name+' : Bytes := ['+', '.join(str(n) for n in literals[name].encode('ascii'))+']\n'
lean+='''
theorem source_key_bytes_separate :
    nullifierBytes ≠ treeBytes ∧ nullifierBytes ≠ notesBytes ∧ nullifierBytes ≠ volumeBytes := by decide

theorem projected_source_keys_separate (project : Bytes → Nat) (injection : Function.Injective project) :
    project nullifierBytes ≠ project treeBytes ∧ project nullifierBytes ≠ project notesBytes ∧
      project nullifierBytes ≠ project volumeBytes := by
  exact ⟨fun same => source_key_bytes_separate.1 (injection same),
    fun same => source_key_bytes_separate.2.1 (injection same),
    fun same => source_key_bytes_separate.2.2 (injection same)⟩

'''+signature+''' := by
  have separate := projected_source_keys_separate project injection
  exact TransferPendingNullifierRetention01.whole_delivery_success_retains_bounded_fresh_pending_nullifier_encoding api keys convert indexAvailable
    raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity (project treeBytes) (project notesBytes) (project volumeBytes)
    payload (project nullifierBytes) entryKey dayKey context action item registryMatches exclusive mode parent queued committed nonempty belowWord
    separate.1 separate.2.1 separate.2.2 success
'''
names=list(literals)+['source_key_bytes_separate','projected_source_keys_separate','whole_success_retains_source_key_pending_nullifier_encoding']
for name in names:
    lean+='\nset_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
lean+='end ShielddSecurity.'+MODULE+'\n'
output=OUT/'generated'/(MODULE+'.lean')
assert not output.exists() and not (OUT/'generation.json').exists()
output.parent.mkdir(parents=True,exist_ok=True); output.write_bytes(lean.encode('utf-8'))
record={'kind':'EXACT_PINNED_OBJECT_KEY_GENERATION_ONLY','output':pin(output),'generator':pin(Path(__file__)),
        'runtime_sources':[pin(v[0]) for v in files.values()],'upstream_contract_source':pin(source),
        'literals':literals,'source_definitions':4,'source_theorems':3,'proof_credit':0,
        'scope':'Generated source identity and exact literal association only; kernel evidence separate. No native, semantic control or certification credit.'}
(OUT/'generation.json').write_bytes((json.dumps(record,sort_keys=True,indent=2)+'\n').encode())
print(json.dumps(record))
