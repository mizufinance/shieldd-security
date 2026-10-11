"""Seal canonical scalar equality with rejected beta-expression attempt preserved."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-complete-block-driver-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-complete-block-driver-20261011-02'", "CURRENT = DIAG / 'transfer-canonical-word-equality-20261011-02'")
s=s.replace('transfer-complete-block-driver-checkpoint-20261011-02','transfer-canonical-word-equality-checkpoint-20261011-02').replace('complete-block-driver-endpoint','canonical-word-equality-endpoint')
replace("MODULE = 'TransferCompleteBlockDriver01'", "MODULE = 'TransferCanonicalWordEquality01'")
replace('assert len(fresh) == 2','assert len(fresh) == 6')
replace("assert pool['objects'] == 100 and len(pool['inherited_public_reports']) == 909", "assert pool['objects'] == 101 and len(pool['inherited_public_reports']) == 911")
replace("manager_endpoint = DIAG / 'transfer-absent-start-publication-endpoint-20261011-01'", "manager_endpoint = DIAG / 'transfer-complete-block-driver-endpoint-20261011-02'")
replace("manager_archive = manager_endpoint / 'portable-windows-absent-start-publication-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-complete-block-driver-endpoint01.tar.xz'")
replace('6a0feb331daf7daea2726d9bd73a3fdd656faf4b76caf48d560fcc5cdde63fb3','351f336d80a662de1e1abbbe37f0584d2cad5bc54f3d3e379c753c2915bacc22')
replace("tar.extractfile('reports/fresh-4-complete-declarations.txt')", "tar.extractfile('reports/fresh-2-complete-declarations.txt')")
replace('assert len(manager_reports) == 4','assert len(manager_reports) == 2')
replace("'module': 'TransferAbsentStartPublication01'", "'module': 'TransferCompleteBlockDriver01'")
replace('assert len(combined_reports) == 909','assert len(combined_reports) == 911')
replace('assert len(manager_selected) == 100','assert len(manager_selected) == 101')
replace("reference = {'absent_start_publication':", "reference = {'complete_block_driver':")
replace("'imported_complete_reports': 4", "'imported_complete_reports': 2")
replace("'complete_owned_modules': 100, 'inherited_complete_reports': 909", "'complete_owned_modules': 101, 'inherited_complete_reports': 911")
s=s.replace('one-hundred-module','one-hundred-one-module').replace('909 original inherited','911 original inherited').replace('verified 909 inherited','verified 911 inherited')
replace("'fresh_definition_audits': 1", "'fresh_definition_audits': 0")
replace("'fresh_structure_audits': 0", "'fresh_structure_audits': 1")
replace("'fresh_theorem_audits': 1", "'fresh_theorem_audits': 5")
replace("'fresh_complete_public_audits': 2", "'fresh_complete_public_audits': 6")
replace("'inherited_complete_public_audits': 909", "'inherited_complete_public_audits': 911")
replace("'fresh_audits': 2, 'inherited_audits': 909", "'fresh_audits': 6, 'inherited_audits': 911",2)
replace("'rejected_attempts': 0", "'rejected_attempts': 1")
s=s.replace('SOURCE_RETURNED_COMPLETE_BLOCK_DRIVER_PUBLICATION_QUALIFIED','SOURCE_CANONICAL_INTERNAL_WORD_MATH_BYTE_EQUALITY_QUALIFIED')
start=s.index("add(CURRENT/'recipe_source.py'");end=s.index("add(stdout, 'reports/fresh-2-complete-declarations.txt'",start)
extra="""add(CURRENT/'recipe_source.py','qualified/recipe_source.py','exact explicit beta-expression proof repair; finite guards unchanged')
failed=DIAG/'transfer-canonical-word-equality-20261011-01'
for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferCanonicalWordEquality01.lean','project/ShielddSecurity/TransferCanonicalWordEquality01.lean','runs/01-TransferCanonicalWordEquality01/stdout.txt']:
    assert pin(failed/n) in plan['pins']
    add(failed/n,'rejected-kernel/01/'+n,'beta-expression rewrite compiler failure; zero proof/control credit')
old=(failed/'handwritten/TransferCanonicalWordEquality01.lean').read_text()
a='      rw [packed_word_cons_division_recovers_exact_tail, packed_word_cons_division_recovers_exact_tail] at tails'
old=old.replace(a,'      change packWords (head :: rest) / radix64 = packWords (other :: tail) / radix64 at tails\\n'+a)
a='    rw [leftRelation, rightRelation, Nat.mod_eq_of_lt left.canonical, Nat.mod_eq_of_lt right.canonical] at packed'
old=old.replace(a,'    change (radix64 ^ 4 * montgomeryValue left.words) % nullifierModulus = (radix64 ^ 4 * montgomeryValue right.words) % nullifierModulus at packed\\n'+a)
assert old==(CURRENT/'handwritten/TransferCanonicalWordEquality01.lean').read_text()
"""
s=s[:start]+extra+s[end:]
replace("add(stdout, 'reports/fresh-2-complete-declarations.txt'", "add(stdout, 'reports/fresh-6-complete-declarations.txt'")
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Six complete full type/axiom reports retained. Failed01 rewrite output retained raw and unselected, zero credit. Fresh02 two explicit beta-expression proof steps leave six contracts unchanged. Canonical domain packWords less than p is explicit; no arbitrary raw-word serializer injectivity claim. Inherited FixedFinalizer list remains its defined model; native source-order correspondence OPEN pending fresh correction. Driver parent manifest has inherited rejected_attempts zero field despite its one raw preserved failed witness; actual count is one and zero credit. Native private Scalar invariant/PartialEq/constant-time primitive/word selector/bytes/hash/Clone/collection/full trace/cache/snapshot/ownership/OS bindings remain explicit. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
replace('returned whole model driver root derives successful reached walk and exact global mathematical input publication','canonical internal raw word equality iff mathematical Montgomery value equality iff source serialized byte equality')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':6,'inherited_reports':911,'owned_modules':101,'rejected_kernel':1})
