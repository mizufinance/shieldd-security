from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
prior=DIAG/'transfer-canonical-source-membership-20261011-01'
s=(prior/'prepare.py').read_text()
needle="POOL = DIAG / 'transfer-canonical-source-membership-owned-floor-20261011-01'"
assert s.count(needle)==1;s=s.replace(needle,"POOL = DIAG / 'transfer-canonical-source-membership-owned-floor-20261011-02'")
note=' First attempt stopped on physical memory pressure after 21.3861752s; original zero-byte stdout, events and complete preparation/source/plan retained with zero proof credit. Fresh same-source attempt uses unchanged physical/commit/process/thread/heartbeat limits; no accepted ancestor replay.'
needle="mapping_file = ROOT / 'source-mapping.json'"
assert s.count(needle)==1;s=s.replace(needle,"mapping['scope'] += "+repr(note)+"\nmapping['interfaces'].append("+repr(note)+")\n"+needle)
needle="plan['artifact_policy'] = "
at=s.index(needle)
s=s[:at]+"pressureMembership=DIAG/'transfer-canonical-source-membership-20261011-01'\nplan['pins'] += [pin(pressureMembership/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferCanonicalSourceMembership01.lean','project/ShielddSecurity/TransferCanonicalSourceMembership01.lean','runs/01-TransferCanonicalSourceMembership01/stdout.txt']]\nplan['source_repairs'] += "+repr(note)+"\n"+s[at:]
(ROOT/'prepare.py').write_text(s)
handwritten=ROOT/'handwritten';handwritten.mkdir(exist_ok=False)
(handwritten/'TransferCanonicalSourceMembership01.lean').write_bytes((prior/'handwritten/TransferCanonicalSourceMembership01.lean').read_bytes())
print({'same_source':True,'pressure_attempt_retained':True,'fresh_reports':6,'limits_unchanged':True})
