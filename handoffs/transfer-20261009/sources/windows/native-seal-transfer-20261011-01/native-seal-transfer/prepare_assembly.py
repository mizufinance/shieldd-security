"""Seal reached native pending transfer; keep failed/withdrawn originals."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-global-commit-join-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-global-commit-join-20261011-01'", "CURRENT = DIAG / 'transfer-native-seal-transfer-20261011-03'")
s=s.replace('transfer-global-commit-join-checkpoint-20261011-01','transfer-native-seal-transfer-checkpoint-20261011-03').replace('global-commit-join-endpoint','native-seal-transfer-endpoint')
replace("MODULE = 'TransferGlobalCommitJoin01'", "MODULE = 'TransferNativeSealTransfer01'")
replace('assert len(fresh) == 5','assert len(fresh) == 3')
replace("assert pool['objects'] == 69 and len(pool['inherited_public_reports']) == 696", "assert pool['objects'] == 71 and len(pool['inherited_public_reports']) == 715")
replace("manager_endpoint = DIAG / 'transfer-end-to-end-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-bounded-native-codec-endpoint-20261011-02'")
replace("manager_archive = manager_endpoint / 'portable-windows-end-to-end-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-bounded-native-codec-endpoint01.tar.xz'")
replace('7d38251e6c29af8105930c8f5d5ac46a3887ff3afa870d1a4e0d29cd03ad5eab','59a11adc6ac2c0a19c8bcfdd34ed06dafc00ab8fb5ae464e9f548819dabff1fd')
replace("tar.extractfile('reports/fresh-13-complete-declarations.txt')", "tar.extractfile('reports/fresh-14-complete-declarations.txt')")
replace('assert len(manager_reports) == 13','assert len(manager_reports) == 14')
replace("'module': 'TransferEndToEnd01'", "'module': 'TransferBoundedNativeCodec01'")
replace('assert len(combined_reports) == 696','assert len(combined_reports) == 715')
replace('assert len(manager_selected) == 69','assert len(manager_selected) == 71')
replace("reference = {'end_to_end':", "reference = {'bounded_native_codec':")
replace("'imported_complete_reports': 13", "'imported_complete_reports': 14")
replace("'complete_owned_modules': 69, 'inherited_complete_reports': 696", "'complete_owned_modules': 71, 'inherited_complete_reports': 715")
s=s.replace('sixty-nine-module','seventy-one-module').replace('696 original inherited','715 original inherited').replace('verified 696 inherited','verified 715 inherited')
replace("add(stdout, 'reports/fresh-5-complete-declarations.txt'", "add(stdout, 'reports/fresh-3-complete-declarations.txt'")
replace("'fresh_definition_audits': 2", "'fresh_definition_audits': 0")
replace("'fresh_complete_public_audits': 5", "'fresh_complete_public_audits': 3")
replace("'inherited_complete_public_audits': 696", "'inherited_complete_public_audits': 715")
replace("'fresh_audits': 5, 'inherited_audits': 696", "'fresh_audits': 3, 'inherited_audits': 715",2)
replace('SOURCE_WHOLE_GLOBAL_INPUTS_TO_HOST_PUBLICATION_UNDER_FINITE_CODEC_AND_FINALIZATION_FIELD_CONTRACT_QUALIFIED','SOURCE_REACHED_NATIVE_SEAL_TRANSFER_EXACT_GLOBAL_INPUT_PUBLICATION_QUALIFIED')
replace("'rejected_attempts': 0", "'rejected_attempts': 1")
anchor="add(stdout, 'reports/fresh-3-complete-declarations.txt'";i=s.index(anchor)
extra="""for suffix, role in [('01','UNRUN withdrawn universal ghost contracts, zero proof credit'),('02','strict failed elaboration, zero whole-proof/control credit')]:
    previous=DIAG/('transfer-native-seal-transfer-20261011-'+suffix)
    names=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','handwritten/TransferNativeSealTransfer01.lean','project/ShielddSecurity/TransferNativeSealTransfer01.lean']
    if suffix=='02':
        names+=['events.jsonl','runs/01-TransferNativeSealTransfer01/stdout.txt']
        failed=[json.loads(line) for line in (previous/'events.jsonl').read_text().splitlines()]
        assert len(failed)==2 and failed[-1]['result']['status']=='failed'
    else: assert not (previous/'events.jsonl').exists()
    for name in names:
        assert pin(previous/name) in plan['pins']
        add(previous/name,'preserved/source'+suffix+'/'+name,role)
"""
s=s[:i]+extra+s[i:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Three original complete full types/axioms retained. Actual reached-state finalization and supported-native getter restrict ghost extension correspondence; ordinary source pipeline directly joins actual native sealed object to exact global inputs. Failed02 and UNRUN01 originals retained with zero whole-proof/control credit. No ancestor/field/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':3,'inherited_reports':715,'owned_modules':71,'rejected_attempts':1})
