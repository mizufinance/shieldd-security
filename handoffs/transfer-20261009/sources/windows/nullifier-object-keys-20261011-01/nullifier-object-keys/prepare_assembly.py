"""Seal exact generated static-key join, regeneration and complete ancestry."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-whole-nullifier-admission-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-whole-nullifier-admission-20261011-01'", "CURRENT = DIAG / 'transfer-nullifier-object-keys-20261011-01'")
s=s.replace('transfer-whole-nullifier-admission-checkpoint-20261011-01','transfer-nullifier-object-keys-checkpoint-20261011-01')
s=s.replace('whole-nullifier-admission-endpoint','nullifier-object-keys-endpoint')
replace("MODULE = 'TransferWholeNullifierAdmission01'", "MODULE = 'TransferNullifierObjectKeys01'")
replace('assert len(fresh) == 6','assert len(fresh) == 7')
replace("assert pool['objects'] == 32 and len(pool['inherited_public_reports']) == 319", "assert pool['objects'] == 34 and len(pool['inherited_public_reports']) == 336")
replace("manager_endpoint = DIAG / 'transfer-deferred-body-failure-endpoint-20261011-03'", "manager_endpoint = DIAG / 'transfer-pending-nullifier-retention-endpoint-20261011-02'")
replace("manager_archive = manager_endpoint / 'portable-windows-deferred-body-failure-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-pending-nullifier-retention-endpoint01.tar.xz'")
replace('1c2258413fcceaeb39e9eb935481c343f72c743e70c6354aabebea34cd74baf3','2f33af5e6067d12f605e3c10ac660729cabc9c1e4c226e02d5ba40e3a0cc3db1')
replace("tar.extractfile('reports/fresh-4-complete-declarations.txt')", "tar.extractfile('reports/fresh-11-complete-declarations.txt')")
replace('assert len(manager_reports) == 4','assert len(manager_reports) == 11')
replace("'module': 'TransferDeferredBodyFailure01'", "'module': 'TransferPendingNullifierRetention01'")
replace('assert len(combined_reports) == 319','assert len(combined_reports) == 336')
replace('assert len(manager_selected) == 32','assert len(manager_selected) == 34')
replace("reference = {'deferred_body_failure':", "reference = {'pending_nullifier_retention':")
replace("'imported_complete_reports': 4", "'imported_complete_reports': 11")
replace("'complete_owned_modules': 32, 'inherited_complete_reports': 319", "'complete_owned_modules': 34, 'inherited_complete_reports': 336")
replace('Exact thirty-two-module closure through both complete-Item body contexts and source-order primitive/index/delivery/deferred joins, with all 319 inherited complete reports.', 'Exact thirty-four-module closure through admitted/retained pending encoding and both complete-Item body/index/deferred branches, with all 336 inherited complete reports.')
replace("add(stdout, 'reports/fresh-6-complete-declarations.txt'", "add(stdout, 'reports/fresh-7-complete-declarations.txt'")
replace("CURRENT / ('handwritten/' + MODULE + '.lean')", "CURRENT / ('generated/' + MODULE + '.lean')")
s=s.replace('installed source backend definition and five complete branch/reshape/whole nullifier admission proofs','generated exact four static source key byte definitions and three separation/whole retained-pending proofs')
s=s.replace('complete thirty-two-module first import root','complete thirty-four-module first import root')
s=s.replace('verified 319 inherited reports','verified 336 inherited reports')
s=s.replace('WHOLE_TRANSFER_DELIVERY_DERIVES_ALL_INPUT_NULLIFIER_ADMISSION_QUALIFIED','EXACT_SOURCE_OBJECT_KEYS_DISCHARGE_WHOLE_PENDING_RETENTION_INEQUALITIES_QUALIFIED')
replace("'fresh_definition_audits': 1", "'fresh_definition_audits': 4")
replace("'fresh_theorem_audits': 5", "'fresh_theorem_audits': 3")
replace("'fresh_complete_public_audits': 6", "'fresh_complete_public_audits': 7")
replace("'inherited_complete_public_audits': 319", "'inherited_complete_public_audits': 336")
start=s.index("    'scope': mapping['scope'] + "); end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"""    'scope': mapping['scope'] + ' Four generated definitions and all three generated theorems have complete original type/axiom reports. Exact pinned Rust literal extraction and independent byte-exact source regeneration are retained. Separation is kernel proved from literal bytes and an explicit equality-preserving projection; hashes identify source bytes and do not prove native semantic correspondence. No generated Lean or evidence was hand-edited.'}
""".rstrip()+s[end:]
s=s.replace("'fresh_audits': 6, 'inherited_audits': 319", "'fresh_audits': 7, 'inherited_audits': 336")
needle="add(ROOT / 'review.json', 'review.json'"
assert s.count(needle)==1
generation="""regen = DIAG / 'transfer-nullifier-object-keys-regeneration-20261011-01'
original_generation = json.loads((CURRENT / 'generation.json').read_bytes())
regenerated = json.loads((regen / 'generation.json').read_bytes())
generated_source = CURRENT / ('generated/' + MODULE + '.lean')
assert original_generation['output'] == pin(generated_source)
assert regenerated['output'] == pin(regen / ('generated/' + MODULE + '.lean'))
assert generated_source.read_bytes() == (regen / ('generated/' + MODULE + '.lean')).read_bytes()
assert original_generation['generator'] == regenerated['generator'] == pin(CURRENT / 'generate.py')
assert original_generation['literals'] == regenerated['literals']
for row in original_generation['runtime_sources'] + [original_generation['upstream_contract_source']]:
    assert pin(row['path']) == row and row in plan['pins']
for name in ['generate.py', 'generation.json']:
    add(CURRENT / name, 'qualified/' + name, 'maintained exact pinned Rust literal/qualified contract generator; no hand-edited output')
add(regen / 'generation.json', 'regeneration/generation.json', 'independent byte-exact generated source identity')
add(regen / ('generated/' + MODULE + '.lean'), 'regeneration/ShielddSecurity/' + MODULE + '.lean', 'independent identical generated Lean source')
"""
s=s.replace(needle,generation+needle)
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':7,'inherited_reports':336,'owned_modules':34,'regeneration_exact':True})
