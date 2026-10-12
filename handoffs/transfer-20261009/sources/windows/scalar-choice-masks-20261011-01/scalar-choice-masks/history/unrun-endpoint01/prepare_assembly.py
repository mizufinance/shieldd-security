from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-pow-field-endpoint-20261012-08/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-scalar-pow-field-20261012-08'","CURRENT = DIAG / 'transfer-scalar-choice-masks-20261012-01'"),
 ("CHECKPOINT = DIAG / 'transfer-scalar-pow-field-checkpoint-20261012-08'","CHECKPOINT = DIAG / 'transfer-scalar-choice-masks-checkpoint-20261012-01'"),
 ("MODULE = 'TransferScalarPowField01'","MODULE = 'TransferScalarChoiceMasks01'"),
 ("archive = ROOT / 'portable-windows-scalar-pow-field-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-scalar-choice-masks-endpoint01.tar.xz'"),
 ('assert len(fresh) == 6','assert len(fresh) == 20'),
 ("assert declaration_kinds.count('inductive') == 0 and declaration_kinds.count('def') == 0 and declaration_kinds.count('theorem') == 6","assert declaration_kinds.count('inductive') == 0 and declaration_kinds.count('structure') == 1 and declaration_kinds.count('def') == 8 and declaration_kinds.count('theorem') == 11"),
 ("add(stdout, 'reports/fresh-6-complete-declarations.txt'","add(stdout, 'reports/fresh-20-complete-declarations.txt'")]:replace(a,b)
start=s.index('for attempt in [1,2,3,4,5,6,7]:');end=s.index("row=mapping['scalar_invert_field_source_shape']",start)
context="""for key,filename in [('scalar_choice_masks_source_shape','scalar-choice-masks-shape.json'),('scalar_pow_bit_integer_source_shape','scalar-pow-bit-integer-shape.json')]:
    row=mapping[key];assert pin(row['path'])==row and row in plan['pins']
    add(row['path'],'context/'+filename,'exact locked word masks and Scalar source associations; general Choice byte invariant explicit, source pow byte invariant derived')
choiceContext=json.loads((CURRENT/'context/scalar-choice-masks-shape.json').read_text())
for key,name in [('subtle_source_copy','subtle-2.6.1-lib.rs'),('subtle_locked_archive','subtle-2.6.1.crate')]:
    row=choiceContext[key];assert pin(row['path'])==row and row in plan['pins']
    add(row['path'],'context/'+name,'exact existing locked crate/source; archive checksum matched runtime Cargo.lock and source matched original archive')
row=choiceContext['locked_cargo_manifest'];assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'runtime/Cargo.lock','exact locked runtime dependency checksum authority')
"""
s=s[:start]+context+s[end:]
start=s.index("for endpoint,names in [(3,");end=s.index("add(Path(__file__), 'assemble.py'",start)
s=s[:start]+s[end:]
start=s.index("    'scope': mapping['scope'] + '");end=s.index("}\ndump(ROOT / 'review.json'",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Twenty complete declarations:one structure/eight definitions/eleven theorems. Exact xor/negative-mask source word and whole Scalar selection equals the documented0/1 branch; canonical output derived from operands; actual modeled power shift/mask cast derives Choice0/1 and the whole masked power loop equals the qualified Boolean source model. Complete existing163-module1296-report word pool reused readonly without new copies or ancestor replay. Exact locked subtle archive/source included. Rust compiler/volatile barrier/ct_eq/caller origins/timing/full Transfer remain open.'"+s[end:]
s=s.replace("'status': 'SOURCE_SCALAR_POWER_EXACT_MATHEMATICAL_FIELD_VALUE_QUALIFIED'","'status': 'SOURCE_LOCKED_CHOICE_WORD_MASKS_AND_POWER_BRANCH_CORRESPONDENCE_QUALIFIED'")
s=s.replace("'rejected_attempts': 3, 'withdrawn_unrun_sources': 3, 'unprepared_setup_failures': 1","'rejected_attempts': 0, 'withdrawn_unrun_sources': 0, 'unprepared_setup_failures': 0")
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-choice-masks-checkpoint-20261012-01';checkpoint.mkdir()
shutil.copyfile(DIAG/'transfer-scalar-inverse-correctness-checkpoint-20261012-04/preservation_check.py',checkpoint/'preservation_check.py')
print({'whole_owned_modules':163,'inherited_reports':1296,'fresh_public_declarations':20,'structure':1,'definitions':8,'theorems':11,'no_new_object_copies':True,'assembly_not_run':True})
