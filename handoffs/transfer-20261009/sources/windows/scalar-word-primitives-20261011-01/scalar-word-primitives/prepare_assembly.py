"""Seal finite-word source arithmetic and all exact rejected/unrun predecessors."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-serialization-range-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-scalar-serialization-range-20261011-02'", "CURRENT = DIAG / 'transfer-scalar-word-primitives-20261011-03'")
s=s.replace('transfer-scalar-serialization-range-checkpoint-20261011-02','transfer-scalar-word-primitives-checkpoint-20261011-03').replace('scalar-serialization-range-endpoint','scalar-word-primitives-endpoint')
replace("MODULE = 'TransferScalarSerializationRange01'", "MODULE = 'TransferScalarWordPrimitives01'")
replace('assert len(fresh) == 8','assert len(fresh) == 10')
replace("assert pool['objects'] == 78 and len(pool['inherited_public_reports']) == 738", "assert pool['objects'] == 79 and len(pool['inherited_public_reports']) == 746")
replace("manager_endpoint = DIAG / 'transfer-native-only-publication-endpoint-20261011-01'", "manager_endpoint = DIAG / 'transfer-scalar-serialization-range-endpoint-20261011-02'")
replace("manager_archive = manager_endpoint / 'portable-windows-native-only-publication-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-scalar-serialization-range-endpoint01.tar.xz'")
replace('7c701a3ada374c7c3b585c1837c3137345de471517b126460767d4d31e650496','1f9989bc6e820940f86b249da9c120fedc9383203a083b2f2debffcee57bfda8')
replace("tar.extractfile('reports/fresh-1-complete-declarations.txt')", "tar.extractfile('reports/fresh-8-complete-declarations.txt')")
replace('assert len(manager_reports) == 1','assert len(manager_reports) == 8')
replace("'module': 'TransferNativeOnlyPublication01'", "'module': 'TransferScalarSerializationRange01'")
replace('assert len(combined_reports) == 738','assert len(combined_reports) == 746')
replace('assert len(manager_selected) == 78','assert len(manager_selected) == 79')
replace("reference = {'native_only_publication':", "reference = {'scalar_serialization_range':")
replace("'imported_complete_reports': 1", "'imported_complete_reports': 8")
replace("'complete_owned_modules': 78, 'inherited_complete_reports': 738", "'complete_owned_modules': 79, 'inherited_complete_reports': 746")
s=s.replace('seventy-eight-module','seventy-nine-module').replace('738 original inherited','746 original inherited').replace('verified 738 inherited','verified 746 inherited')
replace("'fresh_definition_audits': 3", "'fresh_definition_audits': 4")
replace("'fresh_theorem_audits': 5", "'fresh_theorem_audits': 6")
replace("'fresh_complete_public_audits': 8", "'fresh_complete_public_audits': 10")
replace("'inherited_complete_public_audits': 738", "'inherited_complete_public_audits': 746")
replace("'fresh_audits': 8, 'inherited_audits': 738", "'fresh_audits': 10, 'inherited_audits': 746",2)
replace('SOURCE_SCALAR_SERIALIZATION_SYMBOLIC_RANGE_FOUR_U64_ROUNDS_QUALIFIED','SOURCE_SCALAR_FINITE_U64_INPUTS_AND_WIDENED_MAC_ARITHMETIC_QUALIFIED')
replace("add(stdout, 'reports/fresh-8-complete-declarations.txt'", "add(stdout, 'reports/fresh-10-complete-declarations.txt'")
start=s.index("failed=DIAG/'transfer-scalar-serialization-range-20261011-01'");end=s.index("add(stdout, 'reports/fresh-10-complete-declarations.txt'",start)
s=s[:start]+'''failed=DIAG/'transfer-scalar-word-primitives-20261011-02'
for n in ['capture_source.py','prepare_recipe.py','recipe_source.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarWordPrimitives01.lean','project/ShielddSecurity/TransferScalarWordPrimitives01.lean','runs/01-TransferScalarWordPrimitives01/stdout.txt']:
    assert pin(failed/n) in plan['pins']
    add(failed/n,'rejected/02/'+n,'failed original modulo normalization/cast diagnostics; zero proof/control credit')
unrun=DIAG/'transfer-scalar-word-primitives-20261011-01'
for n in ['capture_source.py','prepare_recipe.py','prepare.py','handwritten/TransferScalarWordPrimitives01.lean']:
    assert pin(unrun/n) in plan['pins']
    add(unrun/n,'unrun/01/'+n,'withdrawn source metadata assumption; missing checksum metadata; no plan or Lean/control run')
''' + s[end:]
anchor="mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())"
extra="\nfor row in mapping['word_primitive_context']:\n    assert pin(row['path']) == row and row in plan['pins']\n    add(row['path'], 'context/word-primitive-context/' + Path(row['path']).name, 'raw pinned registry source and authenticated cached crate association, not semantic proof')\n"
s=s.replace(anchor,anchor+extra,1)
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Ten complete full type/axiom reports retained. Failed02 two rewrite mismatches retained with zero credit; fresh03 proof-only modulo repair changes no ten declaration statements or guards. Unrun01 absent Cargo metadata assumption retained, zero executions. The actual cached crate archive and util bytes authenticated against exact clean Cargo.lock; missing metadata was not a semantic control. Lean UInt64/BitVec128 arithmetic model only; actual Rust primitive/carry/sub/byte/trace correspondence remains explicit. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':10,'inherited_reports':746,'owned_modules':79,'rejected_attempts':1,'unrun_predecessors':1})
