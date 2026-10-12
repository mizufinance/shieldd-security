from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
prior=DIAG/'transfer-scalar-choice-masks-endpoint-20261012-05'
assert not (prior/'manifest.json').exists() and not list(prior.glob('*.tar.xz'))
s=(prior/'assemble.py').read_text()
old="add(row['path'],'runtime/Cargo.lock','exact locked runtime dependency checksum authority')"
assert s.count(old)==1
s=s.replace(old,"assert row in mapping['runtime_sources']  # The existing runtime loop archives this exact authority once.")
extra="""priorSealer=DIAG/'transfer-scalar-choice-masks-endpoint-20261012-05'
assert not (priorSealer/'manifest.json').exists() and not list(priorSealer.glob('*.tar.xz'))
for name in ['prepare_assembly.py','assemble.py']:
    add(priorSealer/name,'history/duplicate-archive-key-endpoint05/'+name,'exact original failed assembly recipe; qualification result unchanged and not replayed')
"""
at=s.index("add(Path(__file__), 'assemble.py'");s=s[:at]+extra+s[at:]
(ROOT/'assemble.py').write_text(s)
print({'duplicate_runtime_Cargo_lock_archive_key_removed':True,'exact_lock_authority_archived_by_existing_runtime_loop':True,'same_passed21_declarations':True,'original_failed_sealer_retained':True,'no_proof_replay':True})
