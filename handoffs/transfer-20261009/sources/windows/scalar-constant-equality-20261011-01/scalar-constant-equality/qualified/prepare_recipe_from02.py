from pathlib import Path
import subprocess,sys
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
prior=DIAG/'transfer-scalar-constant-equality-20261012-02'
assert not (ROOT/'prepare.py').exists() and not (prior/'events.jsonl').exists()
(ROOT/'handwritten').mkdir()
old=(prior/'handwritten/TransferScalarConstantEquality01.lean').read_bytes()
before=b'import ShielddSecurity.TransferScalarPowBitInteger01';after=b'import ShielddSecurity.TransferScalarPowInvariant01'
assert old.count(before)==1
(ROOT/'handwritten/TransferScalarConstantEquality01.lean').write_bytes(old.replace(before,after))
for name in ['prepare_recipe.py','prepare_recipe_from01.py']:
    (ROOT/name).write_bytes((prior/name).read_bytes())
subprocess.run([sys.executable,'-B',str(ROOT/'prepare_recipe.py')],check=True)
s=(ROOT/'prepare.py').read_text()
oldImport="'imports': ['ShielddSecurity.TransferScalarPowBitInteger01']"
assert s.count(oldImport)==1
s=s.replace(oldImport,"'imports': ['ShielddSecurity.TransferScalarPowInvariant01']")
start=s.index("mapping['interfaces'] =");end=s.index('\n',start)
s=s[:start]+"mapping['interfaces'] = prior_mapping['interfaces'] + ['Exact locked subtle2.6.1 UInt64 XOR/wrapping negation/OR/high-bit equality byte, exact four-word Scalar equality and inverted refusal flag, with all zero/one byte properties derived. Twelve declarations. Direct import narrowed to qualified power invariant for source ZERO; same existing163-module pool retained readonly. Compiler/volatile barrier/caller origins/timing/full Transfer remain open.']"+s[end:]
extra="""plan['pins'].append(pin(ROOT/'prepare_recipe_from02.py'))
unrunEq=DIAG/'transfer-scalar-constant-equality-20261012-02'
assert not (unrunEq/'events.jsonl').exists()
plan['pins'] += [pin(p) for p in sorted(unrunEq.rglob('*')) if p.is_file()]
unrunEqEndpoint=DIAG/'transfer-scalar-constant-equality-endpoint-20261012-02'
plan['pins'] += [pin(unrunEqEndpoint/n) for n in ['prepare_assembly.py','assemble.py']]
plan['pins'].append(pin(DIAG/'transfer-scalar-constant-equality-checkpoint-20261012-02/preservation_check.py'))
"""
at=s.index("plan['artifact_policy']");s=s[:at]+extra+s[at:]
(ROOT/'prepare.py').write_text(s)
print({'narrow_direct_import':'ShielddSecurity.TransferScalarPowInvariant01','all_12_declaration_statements_and_bodies_unchanged':True,'original_prepared_unrun_retained':True,'all_execution_guards_unchanged':True})
