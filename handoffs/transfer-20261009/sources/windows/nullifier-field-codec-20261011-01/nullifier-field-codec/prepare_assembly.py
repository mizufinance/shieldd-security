from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
prior=DIAG/'transfer-nullifier-field-codec-endpoint-20261012-01'
assert not (ROOT/'assemble.py').exists() and not (prior/'manifest.json').exists()
s=(prior/'assemble.py').read_text()
s=s.replace("CURRENT=DIAG/'transfer-nullifier-field-codec-20261012-02'","CURRENT=DIAG/'transfer-nullifier-field-codec-20261012-03'")
s=s.replace("CHECKPOINT=DIAG/'transfer-nullifier-field-codec-checkpoint-20261012-02'","CHECKPOINT=DIAG/'transfer-nullifier-field-codec-checkpoint-20261012-03'")
s=s.replace("'prepare_from01.py'","'prepare_from02.py'")
start=s.index("failed=DIAG/'transfer-nullifier-field-codec-20261012-01'");end=s.index("add(Path(__file__)",start)
new="""for attempt in ['01','02']:
 failed=DIAG/('transfer-nullifier-field-codec-20261012-'+attempt)
 failed_event=json.loads((failed/'events.jsonl').read_text().splitlines()[-1]);assert failed_event['result']['status']=='failed'
 for p in sorted(failed.rglob('*')):
  if p.is_file():
   assert p.suffix not in ['.olean','.ilean','.c','.o'];assert pin(p) in plan['pins']
   add(p,'history/failed'+attempt+'/'+p.relative_to(failed).as_posix(),'exact failed dependent-if or empty-existential simplification and unused-simp reports; raw failures retained, no semantic negative control')
prior=DIAG/'transfer-nullifier-field-codec-endpoint-20261012-01'
assert not (prior/'manifest.json').exists()
add(prior/'assemble.py','history/unrun-assembly01/assemble.py','original unrun assembly prepared against earlier attempt; updated before sealing without proof replay')
add(ROOT/'prepare_assembly.py','prepare_assembly.py','exact fresh assembly derivation')
"""
s=s[:start]+new+s[end:];s=s.replace("'rejected_attempts':1","'rejected_attempts':2")
(ROOT/'assemble.py').write_bytes(s.encode())
print({'same10_statements','both_raw_failed_histories_retained','no_guard_change','old_assembly_unrun_retained'})
