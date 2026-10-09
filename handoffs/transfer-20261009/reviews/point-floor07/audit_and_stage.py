from pathlib import Path
import hashlib,json,shutil
if not __debug__:raise RuntimeError('optimized Python forbidden')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
CAN=ROOT/'work/shared-build-handoff';OUT=ROOT/'outputs/mac-weierstrass-order07'
DEST=CAN/'handoffs/transfer-20261009/sources/mac/point-floor07'
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
manifest=OUT/'publication-manifest01.json'
assert sha(manifest)=='8a5584091de0c0b235f9b76de0eddf8b51f38ff30d333b1454c055390ca96e7c'
data=json.loads(manifest.read_text());items=[];observations=[]
for item in data['files']:
    source=ROOT/item['path'];assert sha(source)==item['sha256'] and source.stat().st_size==item['bytes']
    if not item['publication']:continue
    assert source.suffix not in ['.log','.olean','.ilean','.trace','.c','.o'] and '.lake'not in source.parts
    target=DEST/item['path'];target.parent.mkdir(parents=True,exist_ok=True)
    if target.exists():assert sha(target)==item['sha256']
    else:shutil.copyfile(source,target)
    items.append(item)
for module in ['WeierstrassPointImportFloor07','WeierstrassPointOnlyFloor07','WeierstrassOrderOnlyFloor07','WeierstrassPointDirectAudit07']:
    receipt=OUT/f'build-{module}-01.json';report=json.loads(receipt.read_text());log=receipt.with_suffix('.log')
    assert sha(log)==report['log_sha256']
    source=ROOT/'work/mac-weierstrass-order07/project/ShielddSecurity'/f'{module}.lean'
    assert sha(source)==report['source_sha256']
    assert '-j1'in report['command'] and '-M2048'in report['command']
    assert report['timeout_seconds']==240 and report['process_group_rss_limit_bytes']==4294967296
    if report['status']=='passed':
        assert module=='WeierstrassOrderOnlyFloor07' and report['exit']==0 and report['axiom_audits']==1
        assert f"'{module}'" not in log.read_text()
        assert f"'ShielddSecurity.{module}.import_marker' does not depend on any axioms" in log.read_text()
    else:
        assert report['exit']==134 and 'memory_exception'in log.read_text() and not report.get('axiom_audits')
    closure=report['frozen_imports']['official_import_closure']
    assert sha(OUT/closure['manifest_file'])==closure['manifest_sha256']
    observations.append(dict(module=module,status=report['status'],exit=report['exit'],
        receipt_sha256=sha(receipt),log_sha256=sha(log),Point_proof_credit=0))
relative=str(manifest.relative_to(ROOT));target=DEST/relative
target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(manifest,target)
items.append(dict(path=relative,sha256=sha(manifest),bytes=manifest.stat().st_size,category='producer_manifest',publication=True))
(DEST/'manifest.json').write_text(json.dumps(dict(kind='bounded-import-diagnostic-transport',files=items,Point_proof_credit=0,full_transfer='OPEN'),indent=2)+'\n')
review=dict(kind='parent-rehash-and-diagnostic-log-review',producer_manifest_sha256=sha(manifest),
    rehashed_entries=31,observations=observations,
    interpretation='Point import plus marker/direct group-instance audit refused at fixed interpreter memory limit. The exact failure phase is not established by zero output. OrderOnly True marker is an import observation, not a point/order proof.45 concrete Point dependencies remain unbuilt.',
    earlier_parent_attempt='Broad filename glob selected inherited FieldPrimeNode07 receipt without a local log; audit stopped before any review result. Corrected to four exact diagnostic module names.',
    kernel_rerun=False,Point_proof_credit=0,full_transfer='OPEN')
(HERE/'review.json').write_text(json.dumps(review,indent=2)+'\n')
review_dest=CAN/'handoffs/transfer-20261009/reviews/point-floor07'
review_dest.mkdir(exist_ok=True)
for name in ['audit_and_stage.py','review.json']:shutil.copyfile(HERE/name,review_dest/name)
print('PASS',len(items),'transport files; four exact diagnostics; zero Point proof credit')
