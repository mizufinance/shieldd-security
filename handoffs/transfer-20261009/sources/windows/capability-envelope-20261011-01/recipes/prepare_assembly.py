"""Prepare three-source35-audit framing association and completion-status packet."""
import ast
import hashlib
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
DIAG=ROOT.parent
text=(DIAG/'transfer-capability-rows-endpoint-20261010-01/assemble.py').read_text()
start=text.index('STAGES = ');end=text.index('\n\ndef pin',start)
text=text[:start]+"STAGES = [('transfer-proof-admission-20261010-02',1),('transfer-envelope-source-bridge-20261010-01',1),('transfer-capability-envelope-join-20261010-01',1)]"+text[end:]
text=text.replace("len(entries) == 2 and len({e['module'] for e in entries}) == 2", "len(entries) == 3 and len({e['module'] for e in entries}) == 3")
text=text.replace('== 43\n','== 35\n')
start=text.index('for task_name, module, classification in [');end=text.index(']:\n    task =',start)
text=text[:start]+"for task_name, module, classification in [\n    ('transfer-proof-admission-20261010-01','TransferProofAdmissionModel','Constructor-like local unit binder: strict warning rejection')"+text[end:]
text=text.replace("floor = DIAG/'transfer-capability-owned-floor-20261010-01'", "floor = DIAG/'transfer-envelope-owned-floor-20261010-01'")
text=text.replace('transfer-capability-acceptance-20261010-03/source-review.json','transfer-proof-admission-20261010-02/source-review.json')
text=text.replace('acceptance-source-review.json','admission-source-review.json')
text=text.replace('circuits/ShielddSecurity/TransferAcceptance.lean','circuits/ShielddSecurity/TransferProofAdmissionModel.lean')
text=text.replace('inputs/prior-handwritten/TransferAcceptance.lean','inputs/prior-handwritten/TransferProofAdmissionModel.lean')
needle="copy(DIAG/'transfer-sdk-raw-authorization-floor-20261010-01/composition-review.json','owned-import-context/prior432-composition-review.json')"
extra="""copy(DIAG/'transfer-capability-owned-floor-20261010-01/composition-review.json','owned-import-context/prior434-composition-review.json')
copy(DIAG/'transfer-proof-admission-owned-floor-20261010-01/composition-review.json','owned-import-context/prior436-composition-review.json')
for layer in ['transfer-proof-admission-owned-floor-20261010-01','transfer-envelope-owned-floor-20261010-01']:
    for name in ['prepare.py','prepare_recipe.py','predecessor_prepare.py']:
        copy(DIAG/layer/name,'owned-import-context/'+layer+'/'+name)
copy(Path('C:/src/shieldd-formal/circuits/ShielddSecurity/TransferEnvelopeSourceBridge.lean'),'inputs/prior-handwritten/TransferEnvelopeSourceBridge.lean')
copy(Path('C:/src/shieldd-pr160-844389ee/crates/crypto/circuits/src/proof.rs'),'source-provenance/runtime/crates/crypto/circuits/src/proof.rs')
copy(DIAG/'transfer-completion-status-20261010-01/status.json','completion-status/status.json')
copy(DIAG/'transfer-completion-status-20261010-01/collect_status.py','completion-status/collect_status.py')
"""
assert needle in text;text=text.replace(needle,extra)
text=text.replace('transfer-capability-rows-checkpoint-20261010-01','transfer-capability-envelope-checkpoint-20261010-01')
text=text.replace("parent = DIAG/'transfer-sdk-raw-authorization-endpoint-20261010-01'", "parent = DIAG/'transfer-capability-rows-endpoint-20261010-01'")
text=text.replace('sdk-raw-authorization-parent-manifest.json','capability-rows-parent-manifest.json')
text=text.replace('sdk_raw_authorization_parent_archive','capability_rows_parent_archive')
text=text.replace('portable-windows-sdk-raw-authorization-endpoint01.tar.xz','portable-windows-capability-rows-endpoint01.tar.xz')
text=text.replace('CONSTRUCTIVE_TRANSACTION_CAPABILITY_ROW_VALIDATION','CONSTRUCTIVE_CAPABILITY_ENVELOPE_ASSOCIATION')
text=text.replace("'source_files':2,'handwritten_sources':2", "'source_files':3,'handwritten_sources':3")
text=text.replace("'type_axiom_pairs':43", "'type_axiom_pairs':35")
text=text.replace('cb017c0e77791e5b12fb3e386b0ced9165374d76','67aa4dc327946667d0a542851470dd2e0d33cd2b')
start=text.index("    'scope':");end=text.index("    'guard_delta':",start)
scope='Verification provenance from individual or separately fresh-randomized batch framing programs composes with successful constructive slot validation. Every expected slot has the exact retained-envelope decoded claim, independently checked location family, selected local relation, singleton statement and one commitment shape. No BoundRows, desired item/coverage/claim equation, proof knowledge or per-entry batch cryptographic consequence is assumed. Primitive Rust extraction/container/codec/deployed-key/crypto and full Transfer circuit/native/state/durable-recovery joins remain OPEN. A read-only retained3130/native-suite/runtime-state milestone is included without new replay or semantic credit.'
text=text[:start]+"    'scope':"+repr(scope)+',\n'+text[end:]
text=text.replace('Two runner bodies','Three runner bodies')
text=text.replace("archive=ROOT/'portable-windows-capability-rows-endpoint01.tar.xz'", "archive=ROOT/'portable-windows-capability-envelope-endpoint01.tar.xz'")
text=text.replace("'sources':2,'audits':43", "'sources':3,'audits':35")
ast.parse(text)
assert not (ROOT/'assemble.py').exists()
(ROOT/'assemble.py').write_text(text,encoding='utf-8',newline='\n')
print('Three-source35-audit capability/envelope packet recipe prepared; fresh preservation required.')
