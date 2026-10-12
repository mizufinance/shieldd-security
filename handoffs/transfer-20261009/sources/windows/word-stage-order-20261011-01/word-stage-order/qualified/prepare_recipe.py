from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
prior=DIAG/'transfer-word-stage-order-20261011-01'
s=(prior/'prepare.py').read_text()
needle="POOL = DIAG / 'transfer-word-stage-order-owned-floor-20261011-01'"
assert s.count(needle)==1;s=s.replace(needle,"POOL = DIAG / 'transfer-word-stage-order-owned-floor-20261011-02'")
note=' First staging attempt stopped on physical pressure after 21.8694105s, zero stdout and no audited/object credit. Original source/preparation/plan/events retained; fresh same-source attempt keeps every physical/commit/process/thread/heartbeat/byte/time guard unchanged, no accepted ancestor replay.'
needle="mapping_file = ROOT / 'source-mapping.json'"
assert s.count(needle)==1;s=s.replace(needle,"mapping['scope'] += "+repr(note)+"\nmapping['interfaces'].append("+repr(note)+")\n"+needle)
at=s.index("plan['artifact_policy'] = ")
s=s[:at]+"pressureStage=DIAG/'transfer-word-stage-order-20261011-01'\nplan['pins'] += [pin(pressureStage/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordStageOrder01.lean','project/ShielddSecurity/TransferWordStageOrder01.lean','runs/01-TransferWordStageOrder01/stdout.txt']]\nplan['source_repairs'] += "+repr(note)+"\n"+s[at:]
(ROOT/'prepare.py').write_text(s)
handwritten=ROOT/'handwritten';handwritten.mkdir(exist_ok=False)
(handwritten/'TransferWordStageOrder01.lean').write_bytes((prior/'handwritten/TransferWordStageOrder01.lean').read_bytes())
print({'same_source':True,'pressure_attempt_retained':True,'fresh_reports':8,'limits_unchanged':True})
