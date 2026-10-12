from pathlib import Path
import hashlib
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-invert-chain-endpoint-20261011-02/prepare_assembly.py'
assert hashlib.sha256(OLD.read_bytes()).hexdigest()=='d26663fcd9dc2fdc322dd9fdfdda094137389724c007fbb98f62ac00b15351d8'
s=OLD.read_text().replace("CURRENT = DIAG / 'transfer-scalar-invert-chain-20261011-02'","CURRENT = DIAG / 'transfer-scalar-invert-chain-20261011-04'").replace('transfer-scalar-invert-chain-checkpoint-20261011-02','transfer-scalar-invert-chain-checkpoint-20261011-04')
exec(compile(s,str(OLD),'exec'),{'__file__':str(ROOT/'prepare_assembly.py')})
s=(ROOT/'assemble.py').read_text()
s=s.replace('assert len(fresh) == 9','assert len(fresh) == 12').replace("assert declaration_kinds.count('def') == 3 and declaration_kinds.count('theorem') == 6","assert declaration_kinds.count('def') == 6 and declaration_kinds.count('theorem') == 6").replace("add(stdout, 'reports/fresh-9-complete-declarations.txt'","add(stdout, 'reports/fresh-12-complete-declarations.txt'")
start=s.index("prior=DIAG/'transfer-scalar-invert-chain-20261011-01'");end=s.index("row=mapping['scalar_invert_chain_source_shape']",start)
s=s[:start]+"""for attempt in [1,2,3]:
    prior=DIAG/('transfer-scalar-invert-chain-20261011-0'+str(attempt))
    names=['generate_source.py','prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-invert-chain-shape.json','generated/TransferScalarInvertChain01.lean','project/ShielddSecurity/TransferScalarInvertChain01.lean']
    if attempt>1: names.append('runs/01-TransferScalarInvertChain01/stdout.txt')
    else: assert not (prior/'runs/01-TransferScalarInvertChain01/stdout.txt').exists()
    for name in names:
        row=pin(prior/name)
        assert row in plan['pins']
        add(prior/name,'prior-invert-chain-attempt0'+str(attempt)+'/'+name,'original physical pressure or recursive-proposition/nested-decidability Lean proof failures;35 original raw artifacts total, no failures treated as successful controls')
oldAssembly=DIAG/'transfer-scalar-invert-chain-endpoint-20261011-02/prepare_assembly.py'
assert pin(oldAssembly)['sha256']=='d26663fcd9dc2fdc322dd9fdfdda094137389724c007fbb98f62ac00b15351d8'
add(oldAssembly,'assembly-history/chain02-unrun-prepare_assembly.py','original unrun source of current assembly derivation; no proof/module result')
"""+s[end:]
s=s.replace("'rejected_attempts': 1, 'withdrawn_unrun_sources': 0, 'unprepared_setup_failures': 0","'rejected_attempts': 3, 'withdrawn_unrun_sources': 0, 'unprepared_setup_failures': 0")
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Twelve complete declarations:six definitions/six theorems. Generated exact85 statement instance has all reads initialized, canonical payload, exact modeled zero refusal and independent natural exponent p-2 certificate. Three small recursive deciders replace nested decidability inference; exact85 source statements/contracts and finite guards unchanged. Original35 raw pressure/proof failure artifacts retained. Generated Lean was regenerated through the repaired generator, never edited directly. Field exponent/inverse/native/full Transfer remain open. No ancestors replayed.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
