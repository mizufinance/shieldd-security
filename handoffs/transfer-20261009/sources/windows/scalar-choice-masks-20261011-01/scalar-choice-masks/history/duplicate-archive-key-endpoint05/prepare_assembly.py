from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-choice-masks-endpoint-20261012-04/assemble.py').read_text()
s=s.replace("CURRENT = DIAG / 'transfer-scalar-choice-masks-20261012-04'","CURRENT = DIAG / 'transfer-scalar-choice-masks-20261012-05'")
s=s.replace("CHECKPOINT = DIAG / 'transfer-scalar-choice-masks-checkpoint-20261012-04'","CHECKPOINT = DIAG / 'transfer-scalar-choice-masks-checkpoint-20261012-05'")
assert s.count('assert len(fresh) == 20')==1
s=s.replace('assert len(fresh) == 20','assert len(fresh) == 21')
s=s.replace("declaration_kinds.count('theorem') == 11","declaration_kinds.count('theorem') == 12")
s=s.replace('fresh-20-complete-declarations','fresh-21-complete-declarations')
s=s.replace('Twenty complete declarations:one structure/eight definitions/eleven theorems.','Twenty-one complete declarations:one structure/eight definitions/twelve theorems, including a reusable Boolean selection lemma to avoid unfolding generated square/multiply bodies during kernel equality checking.')
s=s.replace("'rejected_attempts': 1","'rejected_attempts': 2")
extra="""row=pin(CURRENT/'prepare_recipe_from04.py');assert row in plan['pins']
add(CURRENT/'prepare_recipe_from04.py','qualified/prepare_recipe_from04.py','source repair using abstract Boolean lemma; original theorem statements and guards unchanged')
prior=DIAG/'transfer-scalar-choice-masks-20261012-04'
events04=[json.loads(line) for line in (prior/'events.jsonl').read_text().splitlines()]
assert events04[-1]['result']['reason']=='Lean exit 1'
assert '94:8: error: (kernel) excessive memory consumption detected' in (prior/'runs/01-TransferScalarChoiceMasks01/stdout.txt').read_text()
files=sorted(p for p in prior.rglob('*') if p.is_file());assert len(files)==15
for path in files:
    row=pin(path);assert row in plan['pins']
    add(path,'history/kernel-memory-source04/'+path.relative_to(prior).as_posix(),'exact original kernel memory failure and full raw reports retained; not a successful semantic control')
for label,directory,names in [
    ('unrun-endpoint04','transfer-scalar-choice-masks-endpoint-20261012-04',['prepare_assembly.py','assemble.py']),
    ('checkpoint04','transfer-scalar-choice-masks-checkpoint-20261012-04',['preservation_check.py','preservation.json'])]:
    for name in names:
        path=DIAG/directory/name;assert pin(path) in plan['pins']
        add(path,'history/'+label+'/'+name,'exact original unrun assembly/preservation data retained')
"""
at=s.index("add(Path(__file__), 'assemble.py'");s=s[:at]+extra+s[at:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-choice-masks-checkpoint-20261012-05';checkpoint.mkdir()
shutil.copyfile(DIAG/'transfer-scalar-inverse-correctness-checkpoint-20261012-04/preservation_check.py',checkpoint/'preservation_check.py')
print({'fresh_declarations':21,'structures':1,'definitions':8,'theorems':12,'all_original_failed_history_retained':True,'assembly_not_run':True})
