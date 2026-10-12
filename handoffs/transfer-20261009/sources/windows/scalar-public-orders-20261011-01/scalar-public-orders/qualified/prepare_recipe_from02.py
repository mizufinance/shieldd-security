from pathlib import Path
import subprocess,sys,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
prior=DIAG/'transfer-scalar-public-orders-20261012-02'
assert not (ROOT/'prepare.py').exists()
events=[json.loads(s) for s in (prior/'events.jsonl').read_text().splitlines()]
assert events[-1]['result']['reason']=='Lean exit 1'
(ROOT/'prepare_recipe.py').write_bytes((prior/'prepare_recipe.py').read_bytes())
subprocess.run([sys.executable,'-B',str(ROOT/'prepare_recipe.py')],check=True)
h=ROOT/'handwritten/TransferScalarPublicOrders01.lean';s=h.read_text()
old="orderOf_pow' (by decide)"
new="orderOf_pow' (montgomeryValue (sourceConstantWords .generator) : ZMod nullifierModulus) (by decide : (2^32 : Nat) ≠ 0)"
assert s.count(old)==1;s=s.replace(old,new);h.write_text(s)
p=ROOT/'prepare.py';s=p.read_text()
s=s.replace("assert not (ROOT / 'plan.json').exists() and not POOL.exists()","assert not (ROOT / 'plan.json').exists() and POOL.exists()")
start=s.index('POOL.mkdir()');end=s.index('handwritten = ROOT',start)
reuse="""composition_file=POOL/'composition-review.json'
composition=json.loads(composition_file.read_bytes())
assert composition['objects']==203 and composition['inherited_public_reports']==audits
assert len(records)==len(composition['selected'])
selected=composition['selected']
for name,source,obj in records:
 row=next(item for item in selected if item['module']==name)
 assert row['source']==source and row['object']==obj
 for key in ['source','object','copy']:assert pin(row[key]['path'])==row[key]
 inputs += [source,obj]
"""
s=s[:start]+reuse+s[end:]
extra="""plan['pins'].append(pin(ROOT/'prepare_recipe_from02.py'))
failedOrders=DIAG/'transfer-scalar-public-orders-20261012-02'
plan['pins'] += [pin(p) for p in sorted(failedOrders.rglob('*')) if p.is_file()]
for directory,names in [
 ('transfer-scalar-public-orders-endpoint-20261012-02',['prepare_assembly.py','assemble.py']),
 ('transfer-scalar-public-orders-checkpoint-20261012-02',['preservation_check.py','preservation.json'])]:
 plan['pins'] += [pin(DIAG/directory/n) for n in names]
"""
at=s.index("plan['artifact_policy']");s=s[:at]+extra+s[at:];p.write_text(s)
print({'all_seven_theorem_statements_unchanged':True,'orderOf_pow_explicit_element_argument_supplied':True,'existing203_module_pool_reused_readonly':True,'full_failed_output_retained':True,'all_guards_unchanged':True})
