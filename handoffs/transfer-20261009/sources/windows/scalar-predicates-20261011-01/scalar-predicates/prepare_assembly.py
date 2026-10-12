from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent;prior=DIAG/'transfer-scalar-predicates-endpoint-20261012-01'
assert not (ROOT/'assemble.py').exists() and not (prior/'manifest.json').exists()
s=(prior/'assemble.py').read_text()
s=s.replace("CURRENT=DIAG/'transfer-scalar-predicates-20261012-01'","CURRENT=DIAG/'transfer-scalar-predicates-20261012-02'")
s=s.replace("CHECKPOINT=DIAG/'transfer-scalar-predicates-checkpoint-20261012-01'","CHECKPOINT=DIAG/'transfer-scalar-predicates-checkpoint-20261012-02'")
s=s.replace("['prepare.py','prepare_recipe.py'","['prepare.py','prepare_from01.py','prepare_recipe.py'")
extra="""failed=DIAG/'transfer-scalar-predicates-20261012-01'
assert json.loads((failed/'events.jsonl').read_text().splitlines()[-1])['result']['status']=='failed'
for p in sorted(failed.rglob('*')):
 if p.is_file():
  assert p.suffix not in ['.olean','.ilean','.o','.c'] and pin(p) in plan['pins']
  add(p,'history/failed01/'+p.relative_to(failed).as_posix(),'exact redundant-tactic error and original rejected full types/axioms; no semantic negative control')
prior=DIAG/'transfer-scalar-predicates-endpoint-20261012-01'
assert not (prior/'manifest.json').exists()
for name in ['prepare_assembly.py','assemble.py']:
 add(prior/name,'history/unrun-assembly01/'+name,'original unrun assembly prepared against first failed proof; exact scripts retained')
"""
at=s.index('add(Path(__file__)');s=s[:at]+extra+s[at:]
s=s.replace("'rejected_attempts':0","'rejected_attempts':1")
(ROOT/'assemble.py').write_bytes(s.encode())
print({'same13_statements','original_failed_proof_and_unrun_assembly_retained','no_guard_change'})
