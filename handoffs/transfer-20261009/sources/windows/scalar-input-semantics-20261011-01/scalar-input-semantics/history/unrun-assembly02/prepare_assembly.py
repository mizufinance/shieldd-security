from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent;prior=DIAG/'transfer-scalar-input-semantics-endpoint-20261012-01'
assert not (ROOT/'assemble.py').exists() and not (prior/'assemble.py').exists() and not (prior/'manifest.json').exists()
s=(prior/'prepare_assembly.py').read_text()
s=s.replace("CURRENT=DIAG/'transfer-scalar-input-semantics-20261012-01'","CURRENT=DIAG/'transfer-scalar-input-semantics-20261012-03'")
s=s.replace("CHECKPOINT=DIAG/'transfer-scalar-input-semantics-checkpoint-20261012-01'","CHECKPOINT=DIAG/'transfer-scalar-input-semantics-checkpoint-20261012-03'")
# The template is still unexecuted: retain it and generate the corrected recipe here.
at=s.index("(ROOT/'assemble.py').write_bytes")
extra='''s=s.replace("['prepare.py','prepare_recipe.py'","['prepare.py','prepare_from01.py','prepare_from02.py','prepare_recipe.py'")
history="""failed=DIAG/'transfer-scalar-input-semantics-20261012-01'
assert json.loads((failed/'events.jsonl').read_text().splitlines()[-1])['result']['status']=='failed'
for p in sorted(failed.rglob('*')):
 if p.is_file():
  assert p.suffix not in ['.olean','.ilean','.o','.c'] and pin(p) in plan['pins']
  add(p,'history/failed01/'+p.relative_to(failed).as_posix(),'exact invalid-field elaboration errors and full rejected type/axiom stream, no semantic negative control')
setup=DIAG/'transfer-scalar-input-semantics-20261012-02'
assert not (setup/'prepare.py').exists() and pin(setup/'prepare_from01.py') in plan['pins']
add(setup/'prepare_from01.py','history/setup-failed02/prepare_from01.py','original wrong expected lambda-site count assertion before source/plan generation')
unrun=DIAG/'transfer-scalar-input-semantics-endpoint-20261012-01'
assert not (unrun/'assemble.py').exists() and not (unrun/'manifest.json').exists()
add(unrun/'prepare_assembly.py','history/unrun-assembly01/prepare_assembly.py','original unrun assembly recipe prepared against first failed proof; exact source retained')
"""
at=s.index('add(Path(__file__)');s=s[:at]+history+s[at:]
s=s.replace("'rejected_attempts':0","'rejected_attempts':1")
'''
s=s[:at]+extra+s[at:]
(ROOT/'prepare_assembly_from01.py').write_bytes(s.encode())
print({'original_failed_and_setup_and_unrun_recipe_retained','same7_intended_statements','no_guard_change'})
