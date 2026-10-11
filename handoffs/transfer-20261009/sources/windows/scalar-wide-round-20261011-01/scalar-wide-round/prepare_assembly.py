"""Seal six wide-round contracts with both complete failed attempts retained."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-wide-product-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-scalar-wide-product-20261011-01'", "CURRENT = DIAG / 'transfer-scalar-wide-round-20261011-04'")
s=s.replace('transfer-scalar-wide-product-checkpoint-20261011-01','transfer-scalar-wide-round-checkpoint-20261011-04').replace('scalar-wide-product-endpoint','scalar-wide-round-endpoint')
replace("MODULE = 'TransferScalarWideProduct01'", "MODULE = 'TransferScalarWideRound01'")
replace('assert len(fresh) == 7','assert len(fresh) == 6')
replace("assert pool['objects'] == 109 and len(pool['inherited_public_reports']) == 962", "assert pool['objects'] == 110 and len(pool['inherited_public_reports']) == 969")
replace("manager_endpoint = DIAG / 'transfer-scalar-choice-bit-endpoint-20261011-01'", "manager_endpoint = DIAG / 'transfer-scalar-wide-product-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-scalar-choice-bit-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-scalar-wide-product-endpoint01.tar.xz'")
replace('e6acc6e507544b9eb0182ede867c1f183093ec8ade997bfe530a1b466c3f807a','5444275734646edd75a8b8b3d085dc8babac51e0173bc20b183d30498ed6018f')
replace("tar.extractfile('reports/fresh-8-complete-declarations.txt')", "tar.extractfile('reports/fresh-7-complete-declarations.txt')")
replace('assert len(manager_reports) == 8','assert len(manager_reports) == 7')
replace("'module': 'TransferScalarChoiceBit01'", "'module': 'TransferScalarWideProduct01'")
replace('assert len(combined_reports) == 962','assert len(combined_reports) == 969')
replace('assert len(manager_selected) == 109','assert len(manager_selected) == 110')
replace("reference = {'scalar_choice_bit':", "reference = {'scalar_wide_product':")
replace("'imported_complete_reports': 8", "'imported_complete_reports': 7")
replace("'complete_owned_modules': 109, 'inherited_complete_reports': 962", "'complete_owned_modules': 110, 'inherited_complete_reports': 969")
s=s.replace('one-hundred-nine-module','one-hundred-ten-module').replace('962 original inherited','969 original inherited').replace('verified 962 inherited','verified 969 inherited')
replace("'fresh_theorem_audits': 5", "'fresh_theorem_audits': 4")
replace("'fresh_complete_public_audits': 7", "'fresh_complete_public_audits': 6")
replace("'inherited_complete_public_audits': 962", "'inherited_complete_public_audits': 969")
replace("'fresh_audits': 7, 'inherited_audits': 962", "'fresh_audits': 6, 'inherited_audits': 969",2)
replace("add(stdout, 'reports/fresh-7-complete-declarations.txt'", "add(stdout, 'reports/fresh-6-complete-declarations.txt'")
s=s.replace('SOURCE_SYMBOLIC_SCHOOLBOOK_FULL_WIDE_PRODUCT_QUALIFIED','SOURCE_WIDE_MONTGOMERY_MAC_ADC_DEFERRED_CARRY_QUALIFIED')
needle="mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())"
extra="\nrow = mapping['wide_reduction_source_shape']\nassert pin(row['path']) == row and row in plan['pins']\nadd(row['path'], 'context/wide-reduction-shape.json', 'exact four4MAC/upperADC groups with deferredcarry; static source only')\n"
extra+="for attempt, names in [(1,['prepare_recipe.py','handwritten/TransferScalarWideRound01.lean']),(2,['prepare_recipe.py','recipe_source.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/wide-reduction-shape.json','handwritten/TransferScalarWideRound01.lean','project/ShielddSecurity/TransferScalarWideRound01.lean','runs/01-TransferScalarWideRound01/stdout.txt']),(3,['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/wide-reduction-shape.json','handwritten/TransferScalarWideRound01.lean','project/ShielddSecurity/TransferScalarWideRound01.lean','runs/01-TransferScalarWideRound01/stdout.txt'])]:\n    failed=DIAG/('transfer-scalar-wide-round-20261011-'+str(attempt).zfill(2))\n    for name in names:\n        assert pin(failed/name) in plan['pins']\n        add(failed/name,'unselected/'+str(attempt).zfill(2)+'/'+name,'preserved setup-only or complete failed compiler/pressure attempt; zero proof/control credit')\n"
replace(needle,needle+extra)
replace("'rejected_attempts': 0", "'rejected_attempts': 2")
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Six complete full type/axiom reports retained. Passed fresh04 after setup01 and two failed attempts02/03; all25 original raw files retained and pinned with zero credit. Proof-only beta exposure/named radix bound/unused simp removal preserve six contracts. Actual modeled4MAC low word derives zero; upper ADC retains deferred carry and derives exact full row equation/width. Native primitive/compiler/full trace/final four-round reduction and ignored carry/range/R2 binding remain explicit. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
s=s.replace('symbolic source-shaped full16 MAC product, width and full integer value','exact source-shaped4MAC plusupperADC low cancellation and deferredcarry integer conservation')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':6,'inherited_reports':969,'owned_modules':110,'failed_kernel_attempts':2,'setup_only':1})
