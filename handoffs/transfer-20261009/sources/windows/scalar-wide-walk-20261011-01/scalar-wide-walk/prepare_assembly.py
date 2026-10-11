"""Seal symbolic wide walk, original failed01 source and complete raw reports."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-wide-round-endpoint-20261011-04/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-scalar-wide-round-20261011-04'", "CURRENT = DIAG / 'transfer-scalar-wide-walk-20261011-02'")
s=s.replace('transfer-scalar-wide-round-checkpoint-20261011-04','transfer-scalar-wide-walk-checkpoint-20261011-02').replace('scalar-wide-round-endpoint','scalar-wide-walk-endpoint')
replace("MODULE = 'TransferScalarWideRound01'", "MODULE = 'TransferScalarWideWalk01'")
replace('assert len(fresh) == 6','assert len(fresh) == 7')
replace("assert pool['objects'] == 110 and len(pool['inherited_public_reports']) == 969", "assert pool['objects'] == 111 and len(pool['inherited_public_reports']) == 975")
replace("manager_endpoint = DIAG / 'transfer-scalar-wide-product-endpoint-20261011-01'", "manager_endpoint = DIAG / 'transfer-scalar-wide-round-endpoint-20261011-04'")
replace("manager_archive = manager_endpoint / 'portable-windows-scalar-wide-product-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-scalar-wide-round-endpoint01.tar.xz'")
replace('5444275734646edd75a8b8b3d085dc8babac51e0173bc20b183d30498ed6018f','1be40946950021de2eedf9ddf83647b4c0df14e4790359fb8f424bd503f8fe01')
replace("tar.extractfile('reports/fresh-7-complete-declarations.txt')", "tar.extractfile('reports/fresh-6-complete-declarations.txt')")
replace('assert len(manager_reports) == 7','assert len(manager_reports) == 6')
replace("'module': 'TransferScalarWideProduct01'", "'module': 'TransferScalarWideRound01'")
replace('assert len(combined_reports) == 969','assert len(combined_reports) == 975')
replace('assert len(manager_selected) == 110','assert len(manager_selected) == 111')
replace("reference = {'scalar_wide_product':", "reference = {'scalar_wide_round':")
replace("'imported_complete_reports': 7", "'imported_complete_reports': 6")
replace("'complete_owned_modules': 110, 'inherited_complete_reports': 969", "'complete_owned_modules': 111, 'inherited_complete_reports': 975")
s=s.replace('one-hundred-ten-module','one-hundred-eleven-module').replace('969 original inherited','975 original inherited').replace('verified 969 inherited','verified 975 inherited')
replace("'fresh_theorem_audits': 4", "'fresh_theorem_audits': 5")
replace("'fresh_complete_public_audits': 6", "'fresh_complete_public_audits': 7")
replace("'inherited_complete_public_audits': 969", "'inherited_complete_public_audits': 975")
replace("'fresh_audits': 6, 'inherited_audits': 969", "'fresh_audits': 7, 'inherited_audits': 975",2)
replace("add(stdout, 'reports/fresh-6-complete-declarations.txt'", "add(stdout, 'reports/fresh-7-complete-declarations.txt'")
s=s.replace('SOURCE_WIDE_MONTGOMERY_MAC_ADC_DEFERRED_CARRY_QUALIFIED','SOURCE_SYMBOLIC_WIDE_WALK_MODULAR_VALUE_AND_RANGE_QUALIFIED')
start=s.index('for attempt, names in [');end=s.index("row = mapping['wide_product_source_shape']",start)
s=s[:start]+"failed=DIAG/'transfer-scalar-wide-walk-20261011-01'\nfor name in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarWideWalk01.lean','project/ShielddSecurity/TransferScalarWideWalk01.lean','runs/01-TransferScalarWideWalk01/stdout.txt']:\n    assert pin(failed/name) in plan['pins']\n    add(failed/name,'unselected/01/'+name,'complete original compiler failure retained; zero credit')\n"+s[end:]
replace("'rejected_attempts': 2", "'rejected_attempts': 1")
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Seven complete full type/axiom reports retained. Fresh02 passes after compiler failure01; original ten raw files retained/pinned with zero credit. Proof-only list case rewrite/coefficient grouping/distributivity repair preserves seven contracts. Symbolic induction derives four-word width/Montgomery modulo relation and final value below2p from explicit initial bound. Native primitive/compiler/full trace/private Scalar/ignored carry/normalization/R2 decoder payload remain explicit. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
s=s.replace('exact source-shaped4MAC plusupperADC low cancellation and deferredcarry integer conservation','symbolic wide-state recurrence derives width/modular value and shrinking final range')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':7,'inherited_reports':975,'owned_modules':111,'failed_kernel_attempts':1})
