"""Seal current typed pending read and whole shared-input replay composition."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-nullifier-object-keys-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-nullifier-object-keys-20261011-01'", "CURRENT = DIAG / 'transfer-current-pending-replay-20261011-01'")
s=s.replace('transfer-nullifier-object-keys-checkpoint-20261011-01','transfer-current-pending-replay-checkpoint-20261011-01')
s=s.replace('nullifier-object-keys-endpoint','current-pending-replay-endpoint')
replace("MODULE = 'TransferNullifierObjectKeys01'", "MODULE = 'TransferCurrentPendingReplay01'")
replace('assert len(fresh) == 7','assert len(fresh) == 8')
replace("assert pool['objects'] == 34 and len(pool['inherited_public_reports']) == 336", "assert pool['objects'] == 35 and len(pool['inherited_public_reports']) == 343")
replace("manager_endpoint = DIAG / 'transfer-pending-nullifier-retention-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-nullifier-object-keys-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-pending-nullifier-retention-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-nullifier-object-keys-endpoint01.tar.xz'")
replace('2f33af5e6067d12f605e3c10ac660729cabc9c1e4c226e02d5ba40e3a0cc3db1','4596a11c227ab40856e24f331911de55ebb45b02719abd3b64b6eb195c873f79')
replace("tar.extractfile('reports/fresh-11-complete-declarations.txt')", "tar.extractfile('reports/fresh-7-complete-declarations.txt')")
replace('assert len(manager_reports) == 11','assert len(manager_reports) == 7')
replace("'module': 'TransferPendingNullifierRetention01'", "'module': 'TransferNullifierObjectKeys01'")
replace('assert len(combined_reports) == 336','assert len(combined_reports) == 343')
replace('assert len(manager_selected) == 34','assert len(manager_selected) == 35')
replace("reference = {'pending_nullifier_retention':", "reference = {'nullifier_object_keys':")
replace("'imported_complete_reports': 11", "'imported_complete_reports': 7")
replace("'complete_owned_modules': 34, 'inherited_complete_reports': 336", "'complete_owned_modules': 35, 'inherited_complete_reports': 343")
s=s.replace('Exact thirty-four-module closure through admitted/retained pending encoding and both complete-Item body/index/deferred branches, with all 336 inherited complete reports.', 'Exact thirty-five-module closure through source-derived object keys, retained pending encoding and both complete-Item body/index/deferred branches, with all 343 inherited complete reports.')
replace("add(stdout, 'reports/fresh-7-complete-declarations.txt'", "add(stdout, 'reports/fresh-8-complete-declarations.txt'")
replace("add(CURRENT / ('generated/' + MODULE + '.lean')", "add(CURRENT / ('handwritten/' + MODULE + '.lean')")
s=s.replace('generated exact four static source key byte definitions and three separation/whole retained-pending proofs','current typed object getter and whole two-action shared-input replay refusal')
s=s.replace('complete thirty-four-module first import root','complete thirty-five-module first import root')
s=s.replace('verified 336 inherited reports','verified 343 inherited reports')
s=s.replace('EXACT_SOURCE_OBJECT_KEYS_DISCHARGE_WHOLE_PENDING_RETENTION_INEQUALITIES_QUALIFIED','CURRENT_TYPED_PENDING_READ_DERIVES_SHARED_INPUT_REPLAY_REFUSAL_QUALIFIED')
replace("'fresh_definition_audits': 4", "'fresh_definition_audits': 3")
replace("'fresh_theorem_audits': 3", "'fresh_theorem_audits': 5")
replace("'fresh_complete_public_audits': 7", "'fresh_complete_public_audits': 8")
replace("'inherited_complete_public_audits': 336", "'inherited_complete_public_audits': 343")
start=s.index("    'scope': mapping['scope'] + "); end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' All three definitions and five theorems have complete original type/axiom reports. Whole first success derives actual retained pending membership, and the second body installs the current typed object read. Object representation encode/decode roundtrip remains explicit; wrong-type Rust panics are outside returned results. No native or durable publication correspondence credit.'}"+s[end:]
start=s.index("regen = DIAG / "); end=s.index("add(ROOT / 'review.json'",start)
s=s[:start]+s[end:]
needle="add(ROOT / 'prepare_assembly.py', 'prepare_assembly.py'"
assert s.count(needle)==1
s=s.replace(needle,"add(ROOT / 'prepare_assembly-rejected-selector.py', 'preparation-stopped/prepare_assembly-rejected-selector.py', 'unexecuted sealer preparation selector rejected before assembler creation; zero proof or control credit')\n"+needle)
s=s.replace("'fresh_audits': 7, 'inherited_audits': 336", "'fresh_audits': 8, 'inherited_audits': 343")
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':8,'inherited_reports':343,'owned_modules':35})
