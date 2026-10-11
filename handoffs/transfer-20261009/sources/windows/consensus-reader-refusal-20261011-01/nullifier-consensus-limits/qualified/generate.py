"""Generate the source consensus capacity and narrow whole-delivery joins."""
import hashlib, json, re, sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
OUT=Path(sys.argv[1]).resolve() if len(sys.argv)==2 else ROOT
assert OUT.parent==DIAG and len(sys.argv)<=2
MODULE='TransferNullifierConsensusLimits01'
def pin(p):
    p=Path(p); b=p.read_bytes()
    return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
runtime=Path('C:/src/shieldd-pr160-844389ee/crates/core/component/sct/src/component/tree.rs')
assert pin(runtime)['bytes']==48880 and pin(runtime)['sha256']=='d95558d2c9da8e16419ab1a43c27052d672c607c46bd41b40daa7e9fdf7b1a65'
matches=re.findall(r'pub const MAX_NULLIFIERS_PER_BLOCK:\s*usize\s*=\s*([0-9_]+)\s*;',runtime.read_text())
assert len(matches)==1
capacity=int(matches[0].replace('_',''))
assert capacity==32768
sources={
 'durable':(DIAG/'transfer-whole-durable-readback-20261011-02/handwritten/TransferWholeDurableReadback01.lean',16086,'2969cbe54936308fc37ac79d0f1ec90b5dd70665c136835a3955185a21c2b5ce'),
 'replay':(DIAG/'transfer-current-pending-replay-20261011-01/handwritten/TransferCurrentPendingReplay01.lean',11029,'cef41dded39f050c18d9b73c67090f7b798eb00702842b1c13f25a712e2f820c')}
for p,size,sha in sources.values():
    row=pin(p); assert row['bytes']==size and row['sha256']==sha
lean='''import ShielddSecurity.TransferWholeDurableReadback01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace ShielddSecurity.TransferNullifierConsensusLimits01
set_option autoImplicit false
open TransferStateDelta TransferRawStateProgram01 TransferIndexWriterModel01
open TransferVerificationEqualitySource01 (Item)
open TransferReadback (Store Boundary Status ReadGate MerkleContract)
open TransferNullifierBatchSource01 (Pending)
/-! Generated from the exact pinned Rust consensus capacity and qualified
whole-delivery contracts. Capacity is not a caller-selected model parameter.
Supported 32/64-bit usize representation is explicit; its native target and
Rust arithmetic correspondence remain an interface. The numeric capacity
inequality is derived in the kernel, not assumed. Native typed/reader/proof/
codec/Merkle/token/Host/durability interfaces are preserved unchanged. -/
'''
lean+='\ndef blockCapacity : Nat := '+str(capacity)+'\n'
lean+='''
def nativeWordMax (width : Nat) : Nat := 2 ^ width - 1
def SupportedWidth (width : Nat) : Prop := width = 32 ∨ width = 64

theorem capacity_below_supported_word (width : Nat) (supported : SupportedWidth width) :
    blockCapacity < nativeWordMax width := by
  rcases supported with rfl | rfl <;> decide

'''
wrappers=[
 ('durable','whole_success_every_input_verified_unspent','whole_verified_unspent_at_consensus_capacity',False),
 ('durable','whole_success_every_input_authenticated_absence','whole_authenticated_absence_at_consensus_capacity',True),
 ('replay','first_whole_success_then_shared_input_replay_preserves_first_parent_and_queue','shared_input_replay_at_consensus_capacity',False)]
names=['blockCapacity','nativeWordMax','SupportedWidth','capacity_below_supported_word']
for owner,old,name,merkle in wrappers:
    source=sources[owner][0].read_text()
    signature=source[source.index('theorem '+old):].split(' := by',1)[0]
    signature=signature.replace('theorem '+old,'theorem '+name,1)
    if owner=='durable':
        needle='    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)'
        replacement='    (width : Nat) (supported : SupportedWidth width)\n    (treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)'
    else:
        needle='    (wordMax capacity firstPayload firstEntry firstDay secondPayload secondEntry secondDay : Nat)'
        replacement='    (width : Nat) (supported : SupportedWidth width)\n    (firstPayload firstEntry firstDay secondPayload secondEntry secondDay : Nat)'
    assert signature.count(needle)==1
    signature=signature.replace(needle,replacement)
    assert signature.count(' (belowWord : capacity < wordMax)')==1
    signature=signature.replace(' (belowWord : capacity < wordMax)','')
    identifiers=['installReader','currentReader'] if owner=='durable' else ['withPending']
    namespace='TransferWholeDurableReadback01' if owner=='durable' else 'TransferCurrentPendingReplay01'
    for identifier in identifiers:
        signature=re.sub(r'(?<![A-Za-z0-9_.])'+identifier+r'\b',namespace+'.'+identifier,signature)
    signature=re.sub(r'\bwordMax\b','(nativeWordMax width)',signature)
    signature=re.sub(r'\bcapacity\b','blockCapacity',signature)
    lean+=signature+' := by\n'
    if owner=='durable':
        lean+='  exact TransferWholeDurableReadback01.'+old+''' api keys convert indexAvailable raw notes volume sct volumeAvailable
    decode readerKey readBoundary lockAvailable hash verify candidate '''+('leaves merkle ' if merkle else '')+'''extract inputs outputs
    (nativeWordMax width) blockCapacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey context action item
    registryMatches exclusive mode parent queued committed nonempty (capacity_below_supported_word width supported) success
'''
    else:
        lean+='  exact TransferCurrentPendingReplay01.'+old+''' api keys convert indexAvailable raw notes volume sct volumeAvailable
    decode roundtrip extract inputs outputs project injection (nativeWordMax width) blockCapacity firstPayload firstEntry firstDay
    secondPayload secondEntry secondDay firstContext secondContext firstAction secondAction firstItem secondItem firstRegistry firstExclusive
    secondRegistry secondExclusive firstMode secondMode parent queued firstCommit shared firstMember secondMember
    (capacity_below_supported_word width supported) firstSuccess
'''
    names.append(name)
for name in names:
    lean+='\nset_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
lean+='end ShielddSecurity.'+MODULE+'\n'
output=OUT/'generated'/(MODULE+'.lean')
assert not output.exists() and not (OUT/'generation.json').exists()
output.parent.mkdir(parents=True,exist_ok=True); output.write_bytes(lean.encode('utf-8'))
record={'kind':'EXACT_SOURCE_CONSENSUS_NULLIFIER_CAPACITY_GENERATION_ONLY','output':pin(output),'generator':pin(Path(__file__)),
        'runtime_sources':[pin(runtime)],'upstream_contract_sources':[pin(v[0]) for v in sources.values()],
        'capacity_literal':matches[0],'capacity':capacity,'supported_widths':[32,64],
        'source_definitions':3,'source_theorems':4,'proof_credit':0,
        'scope':'Exact source literal/qualified contract generation only; word-width/native semantics explicit; kernel evidence separate; zero native/control/certification credit.'}
(OUT/'generation.json').write_bytes((json.dumps(record,sort_keys=True,indent=2)+'\n').encode())
print(json.dumps(record))
