from pathlib import Path
import hashlib,contextlib,io
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-invert-chain-endpoint-20261011-04/prepare_assembly.py'
assert hashlib.sha256(OLD.read_bytes()).hexdigest()=='315ebfce862476d57ba1b693bb5fc5cf5c5b4aa66f938548371ea47371eae74f'
s=OLD.read_text().replace("CURRENT = DIAG / 'transfer-scalar-invert-chain-20261011-04'","CURRENT = DIAG / 'transfer-scalar-invert-chain-20261011-05'").replace('transfer-scalar-invert-chain-checkpoint-20261011-04','transfer-scalar-invert-chain-checkpoint-20261011-05')
s=s.replace('for attempt in [1,2,3]:','for attempt in [1,2,3,4]:').replace('35 original raw artifacts total','47 original raw artifacts total').replace("'rejected_attempts': 3,","'rejected_attempts': 4,").replace('Original35 raw pressure/proof failure artifacts retained.','Original47 raw pressure/proof failure artifacts retained; explicit Nat membership type closes the register decider alias.')
with contextlib.redirect_stdout(io.StringIO()):
    exec(compile(s,str(OLD),'exec'),{'__file__':str(ROOT/'prepare_assembly.py')})
s=(ROOT/'assemble.py').read_text();at=s.index("review = {'status':")
s=s[:at]+"""oldAssemblyFourth=DIAG/'transfer-scalar-invert-chain-endpoint-20261011-04/prepare_assembly.py'
assert pin(oldAssemblyFourth)['sha256']=='315ebfce862476d57ba1b693bb5fc5cf5c5b4aa66f938548371ea47371eae74f'
add(oldAssemblyFourth,'assembly-history/chain04-unrun-prepare_assembly.py','original unrun source of current assembly derivation; no proof/module result')
"""+s[at:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':12,'inherited_reports':1257,'owned_modules':157,'original_pressure_and_proof_history_files':47})
