"""Seal exact byte-key cache semantics and retained compiler/pressure/unrun predecessors."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-reversed-byte-order-endpoint-20261011-03/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-scalar-reversed-byte-order-20261011-03'", "CURRENT = DIAG / 'transfer-byte-key-cache-20261011-04'")
s=s.replace('transfer-scalar-reversed-byte-order-checkpoint-20261011-03','transfer-byte-key-cache-checkpoint-20261011-04').replace('scalar-reversed-byte-order-endpoint','byte-key-cache-endpoint')
replace("MODULE = 'TransferScalarReversedByteOrder01'", "MODULE = 'TransferByteKeyCache01'")
replace('assert len(fresh) == 8','assert len(fresh) == 7')
replace("assert pool['objects'] == 104 and len(pool['inherited_public_reports']) == 928", "assert pool['objects'] == 105 and len(pool['inherited_public_reports']) == 936")
replace("manager_endpoint = DIAG / 'transfer-source-ordered-driver-endpoint-20261011-01'", "manager_endpoint = DIAG / 'transfer-scalar-reversed-byte-order-endpoint-20261011-03'")
replace("manager_archive = manager_endpoint / 'portable-windows-source-ordered-driver-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-scalar-reversed-byte-order-endpoint01.tar.xz'")
replace('0f935506e34cb366ab5e08abc1cce3827dc8809127fdb613e727d67361187eec','954d498478cb9749362d35adc6e0521982f6a5571e99b042340950a67f4d8736')
replace("tar.extractfile('reports/fresh-4-complete-declarations.txt')", "tar.extractfile('reports/fresh-8-complete-declarations.txt')")
replace('assert len(manager_reports) == 4','assert len(manager_reports) == 8')
replace("'module': 'TransferSourceOrderedDriver01'", "'module': 'TransferScalarReversedByteOrder01'")
replace('assert len(combined_reports) == 928','assert len(combined_reports) == 936')
replace('assert len(manager_selected) == 104','assert len(manager_selected) == 105')
replace("reference = {'source_ordered_driver':", "reference = {'scalar_reversed_byte_order':")
replace("'imported_complete_reports': 4", "'imported_complete_reports': 8")
replace("'complete_owned_modules': 104, 'inherited_complete_reports': 928", "'complete_owned_modules': 105, 'inherited_complete_reports': 936")
s=s.replace('one-hundred-four-module','one-hundred-five-module').replace('928 original inherited','936 original inherited').replace('verified 928 inherited','verified 936 inherited')
replace("'fresh_definition_audits': 1", "'fresh_definition_audits': 3")
replace("'fresh_theorem_audits': 7", "'fresh_theorem_audits': 4")
replace("'fresh_complete_public_audits': 8", "'fresh_complete_public_audits': 7")
replace("'inherited_complete_public_audits': 928", "'inherited_complete_public_audits': 936")
replace("'fresh_audits': 8, 'inherited_audits': 928", "'fresh_audits': 7, 'inherited_audits': 936",2)
s=s.replace('SOURCE_TYPED_REVERSED_BYTE_SCALAR_ORDER_QUALIFIED','SOURCE_EXACT_BYTE_KEY_CACHE_RELATION_QUALIFIED')
start=s.index("add(CURRENT/'recipe_source.py'");end=s.index("add(stdout, 'reports/fresh-8-complete-declarations.txt'",start)
extra="""add(CURRENT/'recipe_source.py','qualified/recipe_source.py','exact explicit equality cases and application proof repair; finite guards unchanged')
for attempt in ['01','02','03']:
    previous=DIAG/('transfer-byte-key-cache-20261011-'+attempt)
    names=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','handwritten/TransferByteKeyCache01.lean','project/ShielddSecurity/TransferByteKeyCache01.lean']
    if attempt!='01':names.append('recipe_source.py')
    if attempt!='03':names+=['events.jsonl','runs/01-TransferByteKeyCache01/stdout.txt']
    else:assert not (previous/'events.jsonl').exists()
    for n in names:
        assert pin(previous/n) in plan['pins']
        role={'01':'implicit binder compiler failure','02':'physical memory pressure stop','03':'unrun pressure retry plan'}[attempt]
        add(previous/n,'unselected/'+attempt+'/'+n,role+'; no proof/control credit')
old=(DIAG/'transfer-byte-key-cache-20261011-03/handwritten/TransferByteKeyCache01.lean').read_text()
old=old.replace('fun same => TransferInjectiveKeyPublication01.keyCode_is_injective same','fun same => @TransferInjectiveKeyPublication01.keyCode_is_injective left right same')
old=old.replace('  simp only [writeAtBytes, putObject, putByteWrite, encoded_key_equality_iff_exact_byte_key_equality]', '''  change (if keyCode other = keyCode key then some value else delta.cache.objects (keyCode other)) =
    (if other = key then some value else delta.cache.objects (keyCode other))
  by_cases same : other = key
  · rw [if_pos same, if_pos (congrArg keyCode same)]
  · have different : keyCode other ≠ keyCode key := fun equal =>
      same ((encoded_key_equality_iff_exact_byte_key_equality other key).mp equal)
    rw [if_neg same, if_neg different]''')
assert old==(CURRENT/'handwritten/TransferByteKeyCache01.lean').read_text()
"""
s=s[:start]+extra+s[end:]
replace("add(stdout, 'reports/fresh-8-complete-declarations.txt'", "add(stdout, 'reports/fresh-7-complete-declarations.txt'")
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Seven complete full type/axiom reports retained. Failed01 compiler and pressure02 full raw outputs retained zero credit; retry03 never invoked; fresh04 explicit small proof leaves seven contracts unchanged. Exact byte-key semantics are proved under concrete observation maps and global injective renaming, including deletion and no-write distinction. Native String/UTF8/hash-map/Any/Clone/ownership/compiler/cache/full trace bindings remain explicit. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
replace('symbolic reversed typed serializer byte ordering derives exact mathematical scalar comparison','exact byte-key observation relation preserves modeled cache update/delete/overlay/merge semantics')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':7,'inherited_reports':936,'owned_modules':105,'rejected_compiler':1,'pressure':1,'unrun':1})
