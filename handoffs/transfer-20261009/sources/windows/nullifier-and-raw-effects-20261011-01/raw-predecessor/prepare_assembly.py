"""Derive the scoped raw-effects packet from the verified batch packet recipe."""
import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
base = DIAG / 'transfer-nullifier-batch-endpoint-20261011-01/assemble.py'
assert not (ROOT / 'assemble.py').exists() and not (ROOT / 'manifest.json').exists()
source = base.read_text()

def replace(before, after):
    global source
    assert source.count(before) == 1, before
    source = source.replace(before, after)

source = source.replace('nullifier-batch-endpoint', 'raw-effects-endpoint')
source = source.replace('transfer-nullifier-batch-source-20261011-02', 'transfer-raw-effects-source-20261011-03')
source = source.replace('transfer-nullifier-batch-source-20261011-01', 'transfer-raw-effects-source-20261011-02')
source = source.replace('transfer-nullifier-batch-checkpoint', 'transfer-raw-effects-checkpoint')
source = source.replace('TransferNullifierBatchSource01', 'TransferRawEffectsSource01')
source = source.replace('fresh-16-complete-declarations', 'fresh-27-complete-declarations')
replace('assert len(fresh) == 16', 'assert len(fresh) == 27')
replace("assert pool['objects'] == 3 and len(pool['inherited_public_reports']) == 41",
    "assert pool['objects'] == 4 and len(pool['inherited_public_reports']) == 57")
replace("with tarfile.open(raw_archive, 'r:xz') as raw_tar, tarfile.open(vector_archive, 'r:xz') as vector_tar:",
    """batch_root = DIAG / 'transfer-nullifier-batch-endpoint-20261011-01'
batch_archive = batch_root / 'portable-windows-nullifier-batch-endpoint01.tar.xz'
assert pin(batch_archive)['sha256'] == 'd8bf71cf9d7be0fb87cdb1135e7b696638b43c7a38417598d027550d5f0b9411'
with tarfile.open(raw_archive, 'r:xz') as raw_tar, tarfile.open(vector_archive, 'r:xz') as vector_tar, tarfile.open(batch_archive, 'r:xz') as batch_tar:""")
replace("tar = vector_tar if selected['module'] == 'TransferNullifierReaderVector01' else raw_tar",
    "tar = batch_tar if selected['module'] == 'TransferNullifierBatchSource01' else (vector_tar if selected['module'] == 'TransferNullifierReaderVector01' else raw_tar)")
replace("assert {**raw_review['fresh_audits'], **raw_review['inherited_audits'], **vector_review['fresh_audits']} == pool['inherited_public_reports']",
    "batch_review = json.loads(batch_tar.extractfile('review.json').read())\n    assert {**raw_review['fresh_audits'], **raw_review['inherited_audits'], **vector_review['fresh_audits'], **batch_review['fresh_audits']} == pool['inherited_public_reports']")
replace("'inherited_complete_declarations': 41, 'inherited_sources': 3,",
    "'batch': {'status': 'LOCALLY_QUALIFIED_AND_FULLY_TRANSPORTED; PARENT_ACCEPTANCE_SEPARATE', 'archive': pin(batch_archive), 'manifest': pin(batch_root / 'manifest.json')},\n    'inherited_complete_declarations': 57, 'inherited_sources': 4,")
replace("'seven definitions and nine finite reusable batch source proofs'",
    "'twelve definitions and fifteen finite reusable source-order/delivery proofs'")
replace("'complete exact three-module owned import root; object bytes omitted'",
    "'complete exact four-module owned import root; object bytes omitted'")
replace("for name in ['prepare.py', 'plan.json', 'events.jsonl']:",
    "for name in ['prepare.py', 'prepare_successor.py', 'plan.json', 'events.jsonl']:")
replace("for name in ['preservation_check.py', 'preservation.json']:",
    """prior = DIAG / 'transfer-raw-effects-source-20261011-01'
prior_plan = json.loads((prior / 'plan.json').read_bytes())
prior_events = [json.loads(s) for s in (prior / 'events.jsonl').read_text().splitlines()]
prior_stdout = prior / 'runs/01-TransferRawEffectsSource01/stdout.txt'
prior_audits = m.audit(prior_stdout.read_text(), prior_plan['targets'][0]['audit_names'])
assert prior_events[-1]['result']['status'] == 'passed' and len(prior_audits) == 23
assert prior_audits == prior_events[-1]['result']['audits'] and pin(prior_stdout) == prior_events[-1]['result']['stdout']
for name in ['prepare.py', 'plan.json', 'events.jsonl', 'review.json']:
    add(prior / name, 'prior-qualified/' + name, 'preserved original scoped 23-report version; not imported or added to current fresh census')
add(prior / 'handwritten/TransferRawEffectsSource01.lean', 'prior-qualified/source.lean', 'successful earlier callback-interface version; source snapshot unchanged')
add(prior_stdout, 'prior-qualified/complete-23-reports.txt', 'full original qualified declaration reports; not double-counted')
for name in ['preservation_check.py', 'preservation.json']:""")
replace("add(Path(__file__), 'assemble.py', 'exact transport assembly source')",
    "add(ROOT / 'prepare_assembly.py', 'prepare_assembly.py', 'exact fresh assembly derivation source')\nadd(Path(__file__), 'assemble.py', 'exact transport assembly source')")
replace("'PUBLIC_NULLIFIER_BATCH_SOURCE_ORDER_CAPACITY_ALL_INPUT_FRESHNESS_AND_SINGLE_OBJECT_WRITE_QUALIFIED'",
    "'RAW_TRANSFER_CAPTURED_SOURCE_NOTE_EVENT_ORDER_LATE_VOLUME_RECHECK_AND_DELIVERY_DISCARD_QUALIFIED'")
replace("'fresh_sources': 1, 'fresh_definition_audits': 7, 'fresh_theorem_audits': 9,",
    "'fresh_sources': 1, 'fresh_definition_audits': 12, 'fresh_theorem_audits': 15,")
source = source.replace("'fresh_complete_public_audits': 16", "'fresh_complete_public_audits': 27")
source = source.replace("'inherited_complete_public_audits': 41", "'inherited_complete_public_audits': 57")
replace("'interfaces': mapping['interfaces'], 'capacity': mapping['capacity'], 'cache': mapping['cache'], 'order': mapping['order'],",
    "'interfaces': mapping['interfaces'], 'prior_qualified_reports': prior_audits, 'prior_qualified_fresh_census_credit': 0,")
start = source.index("'scope': mapping['scope'] + ")
end = source.index("\ndump(ROOT / 'review.json', review)", start)
source = source[:start] + """'scope': mapping['scope'] + ' Capability mismatch precedes effects. Missing reshape source is checked even for empty inputs. Captured source-id observation is passed to all note callbacks; ordinary volume source is reacquired after note effects. A successful nullifier callback dispatches an exhaustive ordered spend-event loop before any note callback. Note failure retains its failing cache, omits that semantic note-created event and stops the suffix; internal SCT events and partial mutations remain callback behavior. Volume recheck success derives the exact two verifiable [1] writes and their frame, with explicit entry/day key separation. The actual late spent observation after successful reshape derives a raw error retaining earlier child effects, suppression of volume payload insertion, and enclosing delivery rejection with original parent/queue retained. Successful reshape remains an explicit observed upstream interface, not an unconditional runtime theorem. SCT/Merkle, codecs, collection/ownership and durability correspondence remain open. Preserved qualified 01 is not double-counted; failed 02 is zero credit.'}
""".rstrip() + source[end:]
source = source.replace("'fresh_audits': 16", "'fresh_audits': 27").replace("'inherited_audits': 41", "'inherited_audits': 57")
source = source.replace('source-ordered nullifier batch proof', 'raw effect ordering and derived delivery discard proof')
(ROOT / 'assemble.py').write_text(source)
print({'base_recipe_sha256': hashlib.sha256(base.read_bytes()).hexdigest(),
    'fresh_audits': 27, 'inherited_audits': 57, 'retained_prior_qualified': 23, 'rejected_credit': 0})
