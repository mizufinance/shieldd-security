"""Extract exact pinned boundary/legacy key and FORMAT bytes; never patch generated Lean."""
import hashlib, json, re, sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
OUT=Path(sys.argv[1]).resolve() if len(sys.argv)==2 else ROOT
assert OUT.parent==DIAG and len(sys.argv)<=2
MODULE='TransferBoundaryKeyBinding01'
runtime=Path('C:/src/shieldd-pr160-844389ee/crates/core/component/sct/src/permanent_nullifiers/store.rs')
upstream=DIAG/'transfer-stage-boundary-source-20261011-02/handwritten/TransferStageBoundarySource01.lean'
def pin(p):
    p=Path(p); b=p.read_bytes()
    return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
assert pin(runtime)['bytes']==32442 and pin(runtime)['sha256']=='434554cdb4bfb04f37a71707fb0c81ed77ffcf35677a5cab5aaaffd8832cb5a9'
assert pin(upstream)['bytes']==12502 and pin(upstream)['sha256']=='f32fe88937cf10fecc88047412eedd97cf7d6e19b14b48fab25051615dcf6bf9'
text=runtime.read_text()
entries=[('boundaryBytes',r'const BOUNDARY_KEY: &str = "([^"\n]+)";'),
 ('formatKeyBytes',r'const FORMAT_KEY: &str = "([^"\n]+)";'),
 ('rootBytes',r'const ROOT_KEY: &str = "([^"\n]+)";'),
 ('legacyGenerationsBytes',r'\.get_raw\("(sct/nullifier_generations/state)"\)'),
 ('legacySetRootBytes',r'\.get_raw\("(sct/nullifier_set/root)"\)'),
 ('formatValueBytes',r'const FORMAT: &str = "([^"\n]+)";')]
literals={}
for name, pattern in entries:
    matches=re.findall(pattern,text); assert len(matches)==1,(name,len(matches))
    literals[name]=matches[0]; literals[name].encode('ascii')
parts=['import ShielddSecurity.TransferStageBoundarySource01\nset_option maxHeartbeats 200000\nset_option maxRecDepth 4096\nset_option autoImplicit false\nnamespace ShielddSecurity.TransferBoundaryKeyBinding01\nopen TransferStateDelta\nopen TransferReadback (Boundary)\nopen TransferPreparedAcceptedSource01 (Prepared)\nopen TransferStageBoundarySource01 (Keys Io)\n\n/-! Generated exact pinned ASCII boundary/legacy key and FORMAT bytes. An\nexplicit injective key representation derives the three write-key inequalities.\nWhole actual stage success derives original serialization and exact boundary,\nformat and aggregate-root bytes. Hash identity does not certify native getter,\ncodec, SHA256, finite values, ownership, concurrency or publication semantics. -/\n']
for name,_ in entries:
    parts.append('def '+name+' : Bytes := '+str(list(literals[name].encode('ascii')))+'\n')
parts.append(r'''
def sourceKeys (project : Bytes → Nat) : Keys :=
  ⟨project boundaryBytes, project formatKeyBytes, project rootBytes,
    project legacyGenerationsBytes, project legacySetRootBytes⟩

def sourceIo {O : Type} (io : Io O) : Io O := {io with format := formatValueBytes}

theorem source_write_key_bytes_separate :
    boundaryBytes ≠ rootBytes ∧ boundaryBytes ≠ formatKeyBytes ∧ formatKeyBytes ≠ rootBytes := by decide

theorem projected_source_write_keys_separate (project : Bytes → Nat) (injection : Function.Injective project) :
    (sourceKeys project).boundary ≠ (sourceKeys project).root ∧
      (sourceKeys project).boundary ≠ (sourceKeys project).format ∧
      (sourceKeys project).format ≠ (sourceKeys project).root := by
  exact ⟨fun same => source_write_key_bytes_separate.1 (injection same),
    fun same => source_write_key_bytes_separate.2.1 (injection same),
    fun same => source_write_key_bytes_separate.2.2 (injection same)⟩

theorem source_bound_stage_success_records_exact_serialized_next_format_and_root_bytes {O : Type}
    (io : Io O) (project : Bytes → Nat) (injection : Function.Injective project)
    (state : State O) (prepared : Prepared) (staged : State O)
    (success : TransferStageBoundarySource01.stageBoundary (sourceIo io) (sourceKeys project) state prepared = some staged) :
    TransferStageBoundarySource01.ValidTransition prepared ∧
      TransferStageBoundarySource01.ParentAllowed (sourceIo io) (sourceKeys project) state prepared.previous ∧
      ∃ bytes, io.serialize prepared.next = some bytes ∧
        staged.nonverifiable = state.nonverifiable ∧ staged.objects = state.objects ∧
        staged.verifiable (project boundaryBytes) = some bytes ∧
        staged.verifiable (project formatKeyBytes) = some formatValueBytes ∧
        staged.verifiable (project rootBytes) = some (io.commitment prepared.next.roots) := by
  obtain ⟨valid, parent, bytes, serialized, exactState⟩ :=
    TransferStageBoundarySource01.successful_stage_derives_validation_actual_parent_gate_and_serialized_next
      (sourceIo io) (sourceKeys project) state prepared staged success
  subst staged
  have separate := projected_source_write_keys_separate project injection
  have stored := TransferStageBoundarySource01.separated_boundary_keys_receive_exact_serialized_format_and_commitment_bytes
    (sourceIo io) (sourceKeys project) state prepared.next bytes separate.1 separate.2.1 separate.2.2
  exact ⟨valid, parent, bytes, serialized, rfl, rfl, stored.1, stored.2.1, stored.2.2⟩
''')
names=[name for name,_ in entries]+['sourceKeys','sourceIo','source_write_key_bytes_separate',
 'projected_source_write_keys_separate','source_bound_stage_success_records_exact_serialized_next_format_and_root_bytes']
assert len(names)==11
for name in names:
    parts.append('set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n')
parts.append('end ShielddSecurity.'+MODULE+'\n')
p=OUT/'generated'/ (MODULE+'.lean'); assert not p.exists(); p.parent.mkdir(parents=True)
p.write_text('\n'.join(parts))
record={'module':MODULE,'source':pin(p),'runtime':pin(runtime),'upstream':pin(upstream),'generator':pin(__file__),
 'literals':literals,'fresh_audits':11,'native_credit':0,'certification':False}
manifest=OUT/'generation.json'; assert not manifest.exists()
manifest.write_bytes((json.dumps(record,indent=2,sort_keys=True)+'\n').encode())
print(json.dumps(record))
