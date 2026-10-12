from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-choice-masks-endpoint-20261012-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-scalar-choice-masks-20261012-01'","CURRENT = DIAG / 'transfer-scalar-constant-equality-20261012-02'"),
 ("CHECKPOINT = DIAG / 'transfer-scalar-choice-masks-checkpoint-20261012-01'","CHECKPOINT = DIAG / 'transfer-scalar-constant-equality-checkpoint-20261012-02'"),
 ("MODULE = 'TransferScalarChoiceMasks01'","MODULE = 'TransferScalarConstantEquality01'"),
 ("archive = ROOT / 'portable-windows-scalar-choice-masks-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-scalar-constant-equality-endpoint01.tar.xz'"),
 ('assert len(fresh) == 20','assert len(fresh) == 12'),
 ("assert declaration_kinds.count('inductive') == 0 and declaration_kinds.count('structure') == 1 and declaration_kinds.count('def') == 8 and declaration_kinds.count('theorem') == 11","assert declaration_kinds.count('inductive') == 0 and declaration_kinds.count('structure') == 0 and declaration_kinds.count('def') == 4 and declaration_kinds.count('theorem') == 8"),
 ("add(stdout, 'reports/fresh-20-complete-declarations.txt'","add(stdout, 'reports/fresh-12-complete-declarations.txt'")]:replace(a,b)
s=s.replace('scalar_choice_masks_source_shape','scalar_constant_equality_source_shape').replace('scalar-choice-masks-shape.json','scalar-constant-equality-shape.json')
s=s.replace("'prepare_recipe.py', 'execute_bounded.py'","'prepare_recipe.py', 'prepare_recipe_from01.py', 'execute_bounded.py'")
at=s.index("choiceContext=json.loads(")
history="""unprepared=DIAG/'transfer-scalar-constant-equality-20261012-01'
assert not (unprepared/'prepare.py').exists()
for name in ['prepare_recipe.py','handwritten/TransferScalarConstantEquality01.lean']:
    row=pin(unprepared/name);assert row in plan['pins']
    add(unprepared/name,'prior-equality-setup01/'+name,'original setup recipe rejected wrong assumed payload identifier before any source plan/execution; actual t0 source association repaired, theorem source unchanged')
"""
s=s[:at]+history+s[at:]
start=s.index("    'scope': mapping['scope'] + '");end=s.index("}\ndump(ROOT / 'review.json'",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Twelve complete declarations:four definitions/eight theorems. Symbolic uint64 bounds derive exact x OR wrapping-neg high-bit nonzero detection; XOR/high-bit/xor1/cast derives equality bytes, all four byte ANDs derive raw Scalar equality, and actual source Choice NOT flag derives modeled inversion refusal precisely at mathematical zero. No desired equality/flag premise. Complete existing163-module1296-report pool reused readonly without new copies/ancestor replay; exact locked crate/source included. Original2 setup artifacts retained; actual source payload is t0. Rust compiler/volatile barrier/caller origins/timing/full Transfer remain open.'"+s[end:]
s=s.replace("'status': 'SOURCE_LOCKED_CHOICE_WORD_MASKS_AND_POWER_BRANCH_CORRESPONDENCE_QUALIFIED'","'status': 'SOURCE_LOCKED_UNSIGNED_EQUALITY_AND_INVERSION_REFUSAL_FLAG_QUALIFIED'")
s=s.replace("'unprepared_setup_failures': 0","'unprepared_setup_failures': 1")
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-constant-equality-checkpoint-20261012-02';checkpoint.mkdir()
shutil.copyfile(DIAG/'transfer-scalar-inverse-correctness-checkpoint-20261012-04/preservation_check.py',checkpoint/'preservation_check.py')
print({'whole_owned_modules':163,'inherited_reports':1296,'fresh_public_declarations':12,'definitions':4,'theorems':8,'original_setup_files_retained':2,'assembly_not_run':True})
