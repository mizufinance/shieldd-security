"""Prepare one two-source43-audit constructive row-validation packet."""
import ast
from pathlib import Path
ROOT=Path(__file__).resolve().parent
DIAG=ROOT.parent
text=(DIAG/'transfer-sdk-compressed-admission-endpoint-20261010-01/assemble.py').read_text()
start=text.index('STAGES = [');end=text.index('\n\ndef pin',start)
text=text[:start]+"STAGES = [('transfer-capability-acceptance-20261010-03',1),('transfer-capability-rows-20261010-01',1)]"+text[end:]
text=text.replace("len(entries) == 4 and len({e['module'] for e in entries}) == 4", "len(entries) == 2 and len({e['module'] for e in entries}) == 2")
text=text.replace('== 27\n','== 43\n')
start=text.index('for task_name, module, classification in [');end=text.index(']:\n    task =',start)
text=text[:start]+"for task_name, module, classification in [\n    ('transfer-capability-acceptance-20261010-01','TransferAcceptance','Unused Prod.fst simp argument: strict warning rejection'),\n    ('transfer-capability-acceptance-20261010-02','TransferAcceptance','Pair projection not exposed before slot substitution: compiler rejection')"+text[end:]
text=text.replace('transfer-sdk-native-witness-owned-floor-20261010-02','transfer-capability-owned-floor-20261010-01')
start=text.index('for task_name,_ in STAGES:\n    for name in');end=text.index('check = DIAG/',start)
replacement="""for task_name,_ in STAGES:
    copied_names={'prepare.py','prepare_recipe.py','plan.json','review.json','events.jsonl','execute_bounded.py'}
    for path in sorted((DIAG/task_name).iterdir()):
        if path.is_file() and ((path.suffix=='.py' and path.name not in copied_names) or path.name in ['source-review.json','runtime-source-identities.json','predecessor_no_family_source.lean.txt']):
            copy(path,'execution-context/'+task_name+'/'+path.name)
copy(DIAG/'transfer-capability-acceptance-20261010-03/source-review.json','source-provenance/acceptance-source-review.json')
copy(Path('C:/src/shieldd-formal/circuits/ShielddSecurity/TransferAcceptance.lean'),'inputs/prior-handwritten/TransferAcceptance.lean')
runtime_context=json.loads((DIAG/'transfer-capability-rows-20261010-01/runtime-source-identities.json').read_text())
for record in runtime_context['files']:
    assert pin(record['copy']['path'])==record['copy']
    copy(record['copy']['path'],'source-provenance/runtime/'+record['runtime_relative_path'])
copy(DIAG/'transfer-sdk-raw-authorization-floor-20261010-01/composition-review.json','owned-import-context/prior432-composition-review.json')
"""
text=text[:start]+replacement+text[end:]
text=text.replace('transfer-sdk-compressed-admission-checkpoint-20261010-02','transfer-capability-rows-checkpoint-20261010-01')
text=text.replace('transfer-sdk-codec-endpoint-20261010-01','transfer-sdk-raw-authorization-endpoint-20261010-01')
text=text.replace('sdk-codec-parent-manifest.json','sdk-raw-authorization-parent-manifest.json')
text=text.replace('sdk_codec_parent_archive','sdk_raw_authorization_parent_archive')
text=text.replace('portable-windows-sdk-codec-endpoint01.tar.xz','portable-windows-sdk-raw-authorization-endpoint01.tar.xz')
start=text.index("source = DIAG/'transfer-sdk-source-binding");end=text.index("copy(Path(__file__)",start)
text=text[:start]+text[end:]
text=text.replace('SCOPED_MATHEMATICAL_SDK_ENCODING_AND_ADMISSION_NATIVE_CONSTRAINTS','CONSTRUCTIVE_TRANSACTION_CAPABILITY_ROW_VALIDATION')
text=text.replace("'source_files':4,'handwritten_sources':4", "'source_files':2,'handwritten_sources':2")
text=text.replace("'type_axiom_pairs':27", "'type_axiom_pairs':43")
text=text.replace('389ba28b9b42012b619ea735a6ddfe8a205ec7df','cb017c0e77791e5b12fb3e386b0ced9165374d76')
start=text.index("    'scope':");end=text.index("    'guard_delta':",start)
scope='Executable slot-map insertion derives unique keys and retains every original capability. Sorted-key comparison derives exact slot coverage; independent registry, ProofLocation family and exact Item checks derive BoundRows for output map and input rows. Mathematical duplicate/wrong-registry/wrong-item rejection is proved; no runtime negative-control credit is asserted. BoundRows and desired coverage/item equations are not premises of constructor success. Original acceptance interface is qualified with one explicit pair-projection change, and both rejected predecessors remain zero-credit. Rust finite maps/ProofSlot ordering/extracted locations/primitive byte-envelope identity, deployed keys, crypto verification and full Transfer circuit/runtime/state/durability joins remain OPEN.'
text=text[:start]+"    'scope':"+repr(scope)+',\n'+text[end:]
text=text.replace('Four runner bodies','Two runner bodies')
start=text.index("    'open_obligations':");end=text.index("    'runtime_test_credit'",start)
text=text[:start]+"    'open_obligations':['Rust finite-map and bounded ProofSlot representation/order refinement','Native extracted-location/family and exact canonical byte-envelope correspondence','Deployed-key cryptographic verification and full Transfer circuit/runtime/state/durability joins'],\n"+text[end:]
text=text.replace("archive=ROOT/'portable-windows-sdk-compressed-admission-endpoint01.tar.xz'", "archive=ROOT/'portable-windows-capability-rows-endpoint01.tar.xz'")
text=text.replace("'sources':4,'audits':27", "'sources':2,'audits':43")
ast.parse(text)
assert not (ROOT/'assemble.py').exists()
(ROOT/'assemble.py').write_text(text,encoding='utf-8',newline='\n')
print('Two-source43-audit row-constructor packet recipe prepared; fresh preservation required.')
