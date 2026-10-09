"""Freeze reviewable sources and finite pilot receipts; never publish caches/raw captures."""
import hashlib,json
from pathlib import Path
STAGE=Path(__file__).resolve().parent
ROOT=STAGE.parents[1]
OUT=ROOT/'outputs/mac-transfer-pilot01'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
project=STAGE/'project'
packet=json.loads((OUT/'input-packet01.json').read_text())['packet']
modules=packet['topological_import_order']+['TransferCompilerPilotData01',
    'TransferCompilerPilot01','TransferCompilerPilotAudit01','TransferCompilerPilotImportFloor']
chosen=[];history=[]
for module in modules:
    path=project/'ShielddSecurity'/f'{module}.lean';matches=[]
    for receipt in sorted(OUT.glob(f'build-{module}-*.json')):
        value=json.loads(receipt.read_text())
        history.append(dict(receipt=receipt.name,status=value['status'],exit=value.get('exit'),
            reason=value.get('reason'),source_sha256=value['source_sha256'],
            seconds=value.get('seconds'),kernel_or_semantic_control_credit=0
            if value['status']!='passed' else 'scope in pilot-result01.json'))
        if value['status']=='passed' and value['source_sha256']==sha(path):matches.append(receipt)
    assert matches,module
    chosen.append(matches[-1])
audit=json.loads((OUT/'build-TransferCompilerPilotAudit01-03.json').read_text())
assert audit['status']=='passed' and audit['axiom_audits']==77
assert len(audit['full_signature_sha256'])==77
provenance=json.loads((OUT/'provenance-successor01.json').read_text())
assert provenance['status']=='passed'
data=json.loads((OUT/'pilot-data02.json').read_text())
assert data['provenance_receipt_sha256']==sha(OUT/'provenance-successor01.json')
assert 'Ran 9 tests' in (OUT/'audit-tests01.log').read_text() and 'OK' in (OUT/'audit-tests01.log').read_text()
floor=json.loads((OUT/'build-TransferCompilerPilotImportFloor-01.json').read_text())
main=json.loads((OUT/'build-TransferCompilerPilot01-03.json').read_text())
result=dict(status='passed',gate='G2 bounded kernel pilot only',
    pilot_nodes=14,captured_arithmetic_nodes=list(range(8)),captured_assertions=[0],
    captured_row_indices=[0,1,2,3,177954,200767,200768,200769],
    runtime_sha=provenance['runtime_sha'],modulus=provenance['modulus'],
    provenance_receipt_sha256=sha(OUT/'provenance-successor01.json'),
    constructor_proofs='all14 source-node certificates + Boolean assertion certificate',
    reverse_soundness='arbitrary assignment satisfying actual8 rows + verifier column0=1',
    forward_completeness='total assignment satisfying all8 actual rows; all22735 inputs preserved',
    independent_legal_input='input7=0 or input7=1; semantic Bool header join separately owned',
    input_links='public1 to source22734; committed2 to witness6/private9; constant0 tocopy200692',
    audits=dict(unique_fully_qualified_theorems=77,full_signatures=77,standard_axioms_only=True,
        custom_import_source_object_freeze=True,official_import_modules=2802,
        official_import_source_object_metadata_artifact_files=14012,
        official_objects='prebuilt official caches hashed before/after; not locally rebuilt'),
    audit_acceptance_negative_tests=9,
    measured_cost=dict(main_seconds=main['seconds'],main_peak_group_rss_bytes=main['peak_group_rss_bytes'],
        same_import_floor_seconds=floor['seconds'],same_import_floor_rss_bytes=floor['peak_group_rss_bytes'],
        measured_main_minus_floor_rss_bytes=main['peak_group_rss_bytes']-floor['peak_group_rss_bytes'],
        observation='sampled peak RSS difference, not exact Lean heap/marginal allocation'),
    source_dependencies_packet_sha256='cd5ea1f471d047865d2de3a8637087ae775588cce8608087a20954b40898098e',
    full_row_indexed_kernel_instance=False,full_graph_kernel_instance=False,
    selected_projection_hypothesis='ExactIndexedInstance fullRows remains explicit and uninstantiated',
    outlined_arithmetic_term_pilot=False,
    chosen_output='local13 is pilot-selected output; not runtime capture output',
    clean_source_verifier_vk_correspondence='OPEN',full_transfer='OPEN',historical_attempts=history)
target=OUT/'pilot-result01.json';assert not target.exists()
target.write_text(json.dumps(result,indent=2)+'\n')
entries={}
def add(path,relative,classification):
    entries[relative]=dict(local_path=str(path),bytes=path.stat().st_size,sha256=sha(path),classification=classification)
for name in ['generate_pilot.py','generate_audit.py','verify_provenance.py','build_bounded.py',
    'freeze_external.py','audit_log.py','test_audit_log.py','seal_pilot.py']:
    add(STAGE/name,'sources/scripts/'+name,'handwritten generator/proof-checking source')
for name in ['lakefile.lean','lake-manifest.json','lean-toolchain']:
    add(project/name,'sources/circuits/'+name,'frozen dependency package source')
for module in modules:
    kind='frozen dependency proof source' if module in packet['topological_import_order'] else (
        'handwritten proof source' if module=='TransferCompilerPilot01' else 'generated Lean source')
    add(project/'ShielddSecurity'/f'{module}.lean','sources/circuits/ShielddSecurity/'+module+'.lean',kind)
for path in chosen+[OUT/name for name in ['input-packet01.json','pilot-data01.json','pilot-data02.json',
    'audit-roster01.json','provenance-successor01.json','provenance-guarded01.json','pilot-result01.json']]:
    add(path,'receipts/'+path.name,'bounded receipt/data metadata')
add(OUT/'audit-tests01.log','receipts/audit-tests01.txt','finite negative-test result')
manifest=OUT/'publication-manifest01.json';assert not manifest.exists()
manifest.write_text(json.dumps(dict(schema='transfer-mac-kernel-pilot-publication-v1',files=entries,
    excluded='local objects/caches/logs/raw captures/large DB and gzip; failed attempts retained locally',
    full_transfer='OPEN'),indent=2)+'\n')
print(json.dumps(dict(manifest=str(manifest),sha256=sha(manifest),files=len(entries))))
