from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent;prior=DIAG/'transfer-scalar-input-semantics-endpoint-20261012-02'
assert not (ROOT/'assemble.py').exists() and not (prior/'manifest.json').exists()
s=(prior/'assemble.py').read_text()
s=s.replace("CURRENT=DIAG/'transfer-scalar-input-semantics-20261012-03'","CURRENT=DIAG/'transfer-scalar-input-semantics-20261012-04'")
s=s.replace("CHECKPOINT=DIAG/'transfer-scalar-input-semantics-checkpoint-20261012-03'","CHECKPOINT=DIAG/'transfer-scalar-input-semantics-checkpoint-20261012-04'")
s=s.replace("['prepare.py','prepare_from01.py','prepare_from02.py','prepare_recipe.py'","['prepare.py','prepare_from01.py','prepare_from02.py','prepare_from03.py','prepare_recipe.py'")
extra="""failed_second=DIAG/'transfer-scalar-input-semantics-20261012-03'
assert json.loads((failed_second/'events.jsonl').read_text().splitlines()[-1])['result']['status']=='failed'
for p in sorted(failed_second.rglob('*')):
 if p.is_file():
  assert p.suffix not in ['.olean','.ilean','.o','.c'] and pin(p) in plan['pins']
  add(p,'history/failed03/'+p.relative_to(failed_second).as_posix(),'exact higher-order inference/missing import errors and full rejected type/axiom stream, no semantic negative control')
unrun_second=DIAG/'transfer-scalar-input-semantics-endpoint-20261012-02'
assert not (unrun_second/'manifest.json').exists()
for name in ['prepare_assembly.py','prepare_assembly_from01.py','assemble.py']:
 add(unrun_second/name,'history/unrun-assembly02/'+name,'original unrun assembly against second failed proof; original complete scripts retained')
"""
at=s.index('add(Path(__file__)');s=s[:at]+extra+s[at:]
s=s.replace("'rejected_attempts':1","'rejected_attempts':2")
(ROOT/'assemble.py').write_bytes(s.encode())
print({'same7_statements','all_two_failed_proof_and_setup_and_unrun_assembly_histories_retained','no_guard_change'})
