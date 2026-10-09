import hashlib,json,math
from pathlib import Path
STAGE=Path(__file__).resolve().parent;ROOT=STAGE.parents[1]
OUT=ROOT/'outputs/mac-transfer-representative01';PROJECT=STAGE/'project'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
selection=json.loads((OUT/'selection02.json').read_text())
floor=json.loads((OUT/'build-TransferCostImportFloor01-01.json').read_text())
metrics=[];chosen=[]
for block in selection['blocks']:
    name=block['module'];source=PROJECT/'ShielddSecurity'/f'{name}.lean'
    matches=[path for path in sorted(OUT.glob(f'build-{name}-*.json'))
             if (receipt:=json.loads(path.read_text()))['status']=='passed' and receipt['source_sha256']==sha(source)]
    assert matches;path=matches[-1];chosen.append(path);receipt=json.loads(path.read_text())
    assert receipt['axiom_audits']==22 and len(receipt['full_signature_sha256'])==22
    obj=PROJECT/'.lake/build/lib/lean/ShielddSecurity'/f'{name}.olean'
    assert sha(obj)==receipt['object_sha256']
    metrics.append(dict(block,module=name,source_bytes=source.stat().st_size,olean_bytes=obj.stat().st_size,
        wall_seconds=receipt['seconds'],peak_rss_bytes=receipt['peak_group_rss_bytes'],
        sampled_wall_minus_floor_seconds=receipt['seconds']-floor['seconds'],
        sampled_rss_minus_floor_bytes=receipt['peak_group_rss_bytes']-floor['peak_group_rss_bytes'],
        maximum_constructed_remainder_terms=0,producer_receipt=path.name,producer_receipt_sha256=sha(path)))
uniform=1252892/8
result=dict(status='passed',gate='bounded representative cost/interface samples',samples=metrics,
    floor=dict(wall_seconds=floor['seconds'],peak_rss_bytes=floor['peak_group_rss_bytes']),
    observations='sampled total process-group RSS/time; differences are not exact marginal Lean heap/CPU costs',
    all88_named_full_type_and_standard_axiom_audits=True,
    genuine_outlining='middle61550; high172462/172463/172466/172467; no manual row edits',
    proof_scope=dict(node_certificates=32,assertion_certificates=4,
        constructive_arithmetic='all selected arithmetic rows + actual constant-copy link; assertions not claimed complete',
        outside_write_preservation='generic imported theorem instantiated at concrete steps',
        indexed_lookup='local sparse Array rows only; full indexed relation still OPEN',
        semantic_premises='reverse operation soundness requires actual selected-row satisfaction, verifier0=1 and4≠0',
        four='derivable from exact field characteristic as in sealed pilot, but left explicit in cost samples',
        predecessor_ports='typed cut operand contexts; full graph closure deliberately not claimed'),
    rejected_literal8_scaling=dict(modules=math.ceil(uniform),
        uniform_source_bytes_range=[uniform*min(x['source_bytes'] for x in metrics),uniform*max(x['source_bytes'] for x in metrics)],
        uniform_olean_bytes_range=[uniform*min(x['olean_bytes'] for x in metrics),uniform*max(x['olean_bytes'] for x in metrics)],
        floor_wall_seconds_only=math.ceil(uniform)*floor['seconds'],
        label='crude uniform extrapolation, not a reliable whole-program bound; rejects this representation'),
    next='connected registry subgroup nodes1–58/assertions1–6, shared derived expressions and32+26 kernel leaves +small aggregator',
    full_transfer='OPEN',prior_failed_attempt=dict(receipt='build-TransferCostFirst01-01.json',proof_or_control_credit=0,
        reason='generator expression parentheses and free Fin proof-variable elaboration; source snapshot retained'))
path=OUT/'sample-results01.json';assert not path.exists();path.write_text(json.dumps(result,indent=2)+'\n')
files={}
def add(path,relative,kind):files[relative]=dict(local_path=str(path),sha256=sha(path),bytes=path.stat().st_size,classification=kind)
for path in [STAGE/name for name in ['generate_blocks.py','run_prepare.py','build_bounded.py','freeze_external.py','audit_log.py','seal_samples.py']]:add(path,'sources/scripts/'+path.name,'handwritten generator/checker source')
for name in ['lakefile.lean','lake-manifest.json','lean-toolchain']:add(PROJECT/name,'sources/circuits/'+name,'package source')
for name in ['CompilerOrder','CompilerOrderComposition','PoseidonCompletion','CompilerSequenceCompletion']:
    add(PROJECT/'ShielddSecurity'/f'{name}.lean','sources/circuits/ShielddSecurity/'+name+'.lean','frozen maintained proof source')
for name in [x['module'] for x in metrics]+['TransferCostImportFloor01']:
    add(PROJECT/'ShielddSecurity'/f'{name}.lean','sources/circuits/ShielddSecurity/'+name+'.lean','generated cost/interface Lean source')
for path in chosen+[OUT/name for name in ['input-packet01.json','selection02.json','selection-guard02.json','sample-results01.json','build-TransferCostImportFloor01-01.json']]+list(OUT.glob('official-imports-*.json')):
    add(path,'receipts/'+path.name,'receipt or deduplicated official import manifest')
manifest=OUT/'publication-manifest01.json';assert not manifest.exists();manifest.write_text(json.dumps(dict(files=files,
    reused_nine_source_dependency_packet='sealed mac-transfer-pilot01 and cd5ea1f471d047865d2de3a8637087ae775588cce8608087a20954b40898098e',
    inherited_producer_dependencies='copied audited exact source/object identities; local producer receipts retained',
    proof_scope='cost/interface only; fullTransfer OPEN'),indent=2)+'\n')
print(json.dumps(dict(manifest=str(manifest),sha256=sha(manifest),files=len(files))))
