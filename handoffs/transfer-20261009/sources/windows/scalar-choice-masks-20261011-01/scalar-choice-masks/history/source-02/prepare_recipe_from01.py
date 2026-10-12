from pathlib import Path
import subprocess,sys
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
prior=DIAG/'transfer-scalar-choice-masks-20261012-01'
assert not (ROOT/'prepare.py').exists() and not (prior/'events.jsonl').exists()
old=(prior/'handwritten/TransferScalarChoiceMasks01.lean').read_bytes()
before=b'import ShielddSecurity.TransferScalarPowBitInteger01'
after=b'import ShielddSecurity.TransferScalarPowInvariant01'
assert old.count(before)==1
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferScalarChoiceMasks01.lean').write_bytes(old.replace(before,after))
(ROOT/'prepare_recipe.py').write_bytes((prior/'prepare_recipe.py').read_bytes())
subprocess.run([sys.executable,'-B',str(ROOT/'prepare_recipe.py')],check=True)
s=(ROOT/'prepare.py').read_text()
oldImport="'imports': ['ShielddSecurity.TransferScalarPowBitInteger01']"
assert s.count(oldImport)==1
s=s.replace(oldImport,"'imports': ['ShielddSecurity.TransferScalarPowInvariant01']")
start=s.index("mapping['interfaces'] =");end=s.index('\n',start)
s=s[:start]+"mapping['interfaces'] = prior_mapping['interfaces'] + ['Exact locked subtle2.6.1 word-mask selection and four-word Scalar selection, explicit general Choice0/1 contract, derived actual source power shift/mask Choice byte, and whole masked source power loop correspondence. Twenty declarations. Direct import narrowed to the qualified power invariant; same complete163-module pool retained readonly. Compiler/volatile barrier/ct_eq/all caller origins/timing/full Transfer remain open.']"+s[end:]
extra="""plan['pins'].append(pin(ROOT/'prepare_recipe_from01.py'))
unrunChoice=DIAG/'transfer-scalar-choice-masks-20261012-01'
assert not (unrunChoice/'events.jsonl').exists()
unrunChoiceFiles=sorted(p for p in unrunChoice.rglob('*') if p.is_file())
assert len(unrunChoiceFiles)==11
plan['pins'] += [pin(p) for p in unrunChoiceFiles]
unrunChoiceEndpoint=DIAG/'transfer-scalar-choice-masks-endpoint-20261012-01'
plan['pins'] += [pin(unrunChoiceEndpoint/n) for n in ['prepare_assembly.py','assemble.py']]
plan['pins'].append(pin(DIAG/'transfer-scalar-choice-masks-checkpoint-20261012-01/preservation_check.py'))
"""
at=s.index("plan['artifact_policy']");s=s[:at]+extra+s[at:]
(ROOT/'prepare.py').write_text(s)
print({'narrow_direct_import':'ShielddSecurity.TransferScalarPowInvariant01','all_20_declaration_statements_and_bodies_unchanged':True,'unrun_original_retained':True,'all_execution_guards_unchanged':True})
