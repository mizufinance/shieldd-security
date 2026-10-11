"""Prepare generated source record size/read limit model and independent regeneration."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-durable-write-source-20261011-01/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-writer-recovery-join-20261011-01'", "UPSTREAM = DIAG / 'transfer-durable-write-source-20261011-01'")
replace("POOL = DIAG / 'transfer-durable-write-source-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-record-read-bound-owned-floor-20261011-01'")
replace("MODULE = 'TransferDurableWriteSource01'", "MODULE = 'TransferRecordReadBound01'")
replace("stdout = UPSTREAM / 'runs/01-TransferWriterRecoveryJoin01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferDurableWriteSource01/stdout.txt'")
replace("records.append(('TransferWriterRecoveryJoin01'", "records.append(('TransferDurableWriteSource01'")
replace("'handwritten/TransferWriterRecoveryJoin01.lean', 'project/ShielddSecurity/TransferWriterRecoveryJoin01.lean'", "'handwritten/TransferDurableWriteSource01.lean', 'project/ShielddSecurity/TransferDurableWriteSource01.lean'")
replace('assert len(current) == 6','assert len(current) == 8')
replace('assert len(records) == 58 and len(audits) == 576','assert len(records) == 59 and len(audits) == 584')
replace("'objects': 58", "'objects': 59")
s=s.replace('Complete fifty-eight-module first owned root; 576 inherited full reports;', 'Complete fifty-nine-module first owned root; 584 inherited full reports;')
replace("handwritten = ROOT / 'handwritten' / (MODULE + '.lean')", "handwritten = ROOT / 'generated' / (MODULE + '.lean')")
replace("'imports': ['ShielddSecurity.TransferWriterRecoveryJoin01']", "'imports': ['ShielddSecurity.TransferDurableWriteSource01']")
start=s.index('\nmapping = ')+1; end=s.index('\nmapping_file =',start)
scope='Generated exact source MAX_RECORD_BYTES expression 4*1024*1024 and checked source read_record take(MAX_RECORD_BYTES+1)/read_to_end/returned byte length check. Source take limit is one beyond record cap and proved below 32/64-bit word ranges. Whole returned record derives exact observed read_to_end bytes at source take limit and length at most 4194304; oversized returned bytes and read errors refuse without default records. Eight reports (four data/program definitions, four proofs), maintained generator plus byte-identical independent regeneration; finite/physical/strict audit guards unchanged. Native File/Take/Read partial read semantics, allocation/typed u8/usize-to-u64 supported word embedding/ownership/serde/OS state and whole input consumption remain interfaces. Model Nat length reflects native cast only on supported typed 32/64-bit domain. No native/control/full Transfer certification and no semantic-negative-control credit from formal refusal proofs.'
s=s[:start]+"mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ['Generated constant uses restricted arithmetic parsing of exact pinned Rust MAX_RECORD_BYTES expression and asserts source take/read_to_end/size-check return structure. Primitive readToEnd callback carries actual returned bytes or error; take limit passed explicitly. Native file/read/Take consumption or actual returned byte allocation bounds are not assumed from source identity; read errors may have consumed partial data and no physical rollback inferred. Model Nat length check corresponds to native usize as u64 on supported typed 32/64-bit domain; u8 data validity, serde/owner/OS/async correspondence remains explicit. Formal oversized/refusal proof is not an executed negative control.'],\n    'scope': "+repr(scope)+"}"+s[end:]
s=s.replace('SOURCE_DURABLE_FILE_WRITE_ORDER_OBSERVED_PROGRESS_AND_INTENT_FAILURE','SOURCE_RECORD_READ_TAKE_LIMIT_RETURNED_BYTE_BOUND_AND_REFUSALS')
s=s.replace('DURABLE_WRITE_SOURCE_COMPLETE_FIFTY_EIGHT_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','RECORD_READ_BOUND_COMPLETE_FIFTY_NINE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 8, 'inherited_audits': 576", "'fresh_audits': 8, 'inherited_audits': 584")
s=s.replace('complete fifty-eight-module owned root','complete fifty-nine-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh maintained source byte cap/take/read check model and independent exact regeneration; no generated hand edits, ancestor replay or native control credit. Guards unchanged.'"+s[end:]
anchor="plan['pins'] += mapping['runtime_sources']"; assert s.count(anchor)==1
extra="""regenerated = DIAG / 'transfer-record-read-regeneration-20261011-01'
assert (regenerated / 'generated' / (MODULE + '.lean')).read_bytes() == handwritten.read_bytes()
plan['pins'] += [pin(ROOT / 'generate.py'), pin(ROOT / 'generation.json'), pin(regenerated / 'generation.json'), pin(regenerated / 'generated' / (MODULE + '.lean'))]
"""
s=s.replace(anchor,extra+anchor)
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':8,'inherited_audits':584,'owned_modules':59,'regeneration':True})
