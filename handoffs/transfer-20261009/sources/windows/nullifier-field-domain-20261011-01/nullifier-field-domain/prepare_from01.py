from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent;prior=DIAG/'transfer-nullifier-field-domain-endpoint-20261012-01'
assert not (ROOT/'prepare_assembly.py').exists() and not (prior/'assemble.py').exists()
s=(prior/'prepare_assembly.py').read_text()
before=' assert s.count(a)==1,(a,s.count(a));s=s.replace(a,b)'
assert s.count(before)==1
s=s.replace(before," wanted=3 if a=='nullifier-field-codec-shape.json' else 2 if a==\"'fresh_audits':10,'inherited_audits':1473\" else 1\n assert s.count(a)==wanted,(a,s.count(a),wanted);s=s.replace(a,b)")
at=s.index("(ROOT/'assemble.py').write_bytes")
extra='''s=s.replace("CURRENT=DIAG/'transfer-nullifier-field-domain-20261012-01'","CURRENT=DIAG/'transfer-nullifier-field-domain-20261012-02'")
s=s.replace("CHECKPOINT=DIAG/'transfer-nullifier-field-domain-checkpoint-20261012-01'","CHECKPOINT=DIAG/'transfer-nullifier-field-domain-checkpoint-20261012-02'")
s=s.replace("['prepare.py','prepare_recipe.py'","['prepare.py','prepare_from01.py','prepare_recipe.py'")
history="""failed=DIAG/'transfer-nullifier-field-domain-20261012-01'
assert json.loads((failed/'events.jsonl').read_text().splitlines()[-1])['result']['status']=='failed'
for p in sorted(failed.rglob('*')):
 if p.is_file():
  assert p.suffix not in ['.olean','.ilean','.o','.c'] and pin(p) in plan['pins']
  add(p,'history/failed01/'+p.relative_to(failed).as_posix(),'exact raw finite-heartbeat and arithmetic-lemma failure history; unqualified, no semantic negative control')
old_assembly=DIAG/'transfer-nullifier-field-domain-endpoint-20261012-01'
assert not (old_assembly/'assemble.py').exists() and not (old_assembly/'manifest.json').exists()
add(old_assembly/'prepare_assembly.py','history/setup-failed-assembly01/prepare_assembly.py','exact failed archive-recipe token-count assertion before assembly generation')
add(ROOT/'prepare_from01.py','prepare_from01.py','fresh assembly generator correction preserving original failed setup')
"""
at=s.index('add(Path(__file__)');s=s[:at]+history+s[at:]
s=s.replace("'rejected_attempts':0","'rejected_attempts':1")
'''
s=s[:at]+extra+s[at:]
(ROOT/'prepare_assembly.py').write_bytes(s.encode())
print({'exact_token_counts_checked':True,'prior_setup_failure_retained':True,'original_proof_failure_retained':True})
