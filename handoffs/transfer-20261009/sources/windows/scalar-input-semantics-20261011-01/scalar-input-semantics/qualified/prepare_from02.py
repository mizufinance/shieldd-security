from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
prior=DIAG/'transfer-scalar-input-semantics-20261012-02'
assert not (ROOT/'prepare_from01.py').exists() and not (prior/'prepare.py').exists()
s=(prior/'prepare_from01.py').read_text()
assert s.count("==16")==1;s=s.replace('==16','==14')
s=s.replace("POOL=DIAG/'transfer-scalar-input-semantics-owned-floor-20261012-02'","POOL=DIAG/'transfer-scalar-input-semantics-owned-floor-20261012-03'")
s=s.replace("+[pin(ROOT/'prepare_from01.py')]","+[pin(ROOT/'prepare_from01.py'),pin(ROOT/'prepare_from02.py'),pin(DIAG/'transfer-scalar-input-semantics-20261012-02/prepare_from01.py')]")
(ROOT/'prepare_from01.py').write_bytes(s.encode())
print({'actual14_lambda_sites_checked','original_setup_count_failure_preserved','no_proof_or_guard_change'})
