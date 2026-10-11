"""Fresh setup repair: old static table is key inventory, authenticated call positions give order."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
old=DIAG/'transfer-source-ordered-finalizer-20261011-01'
s=(old/'prepare_recipe.py').read_text()
s=s.replace('transfer-source-ordered-finalizer-owned-floor-20261011-01','transfer-source-ordered-finalizer-owned-floor-20261011-02')
a="assert keys==[r['utf8'] for r in association['known_mutation_order']]"
b="""assert keys==[association['known_mutation_order'][i]['utf8'] for i in order]
assert association['call_positions']==sorted(association['call_positions']) and len(association['call_positions'])==5
association['known_mutation_order']=[association['known_mutation_order'][i] for i in order]
association['scope']+=' Fresh table follows authenticated call positions; original inventory order was not call order. Static association only.'
(ROOT/'context').mkdir();(ROOT/'context/corrected-finalization-call-order.json').write_text(json.dumps(association,indent=2,sort_keys=True)+'\\n')"""
assert s.count(a)==1;s=s.replace(a,b)
(ROOT/'recipe_source.py').write_text(s)
exec(compile(s,str(ROOT/'recipe_source.py'),'exec'),{'__file__':str(ROOT/'recipe_source.py'),'__name__':'__main__'})
p=ROOT/'prepare.py';s=p.read_text()
a="[Path(__file__), ROOT / 'prepare_recipe.py', runner";assert s.count(a)==1
s=s.replace(a,"[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner")
a="\ndomain = ";at=s.index(a)
s=s[:at]+"\nmapping['corrected_finalization_source_order']=pin(ROOT/'context/corrected-finalization-call-order.json')\n"+s[at:]
at=s.index("plan['artifact_policy']")
s=s[:at]+"plan['pins'] += [mapping['corrected_finalization_source_order'], pin(DIAG/'transfer-source-ordered-finalizer-20261011-01/prepare_recipe.py')]\nfailedCanonical=DIAG/'transfer-canonical-word-equality-20261011-01'\nplan['pins'] += [pin(failedCanonical/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferCanonicalWordEquality01.lean','project/ShielddSecurity/TransferCanonicalWordEquality01.lean','runs/01-TransferCanonicalWordEquality01/stdout.txt']]\n"+s[at:]
p.write_text(s)
