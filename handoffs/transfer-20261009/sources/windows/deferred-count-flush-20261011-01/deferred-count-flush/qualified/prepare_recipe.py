"""Fresh proof-only flush simplification successor; rejected attempt immutable."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
PRIOR=DIAG/'transfer-deferred-count-flush-20261011-01'
assert not (ROOT/'prepare.py').exists()
events=[json.loads(x) for x in (PRIOR/'events.jsonl').read_text().splitlines()]
assert len(events)==2 and events[-1]['result']['status']=='failed'
s=(PRIOR/'prepare.py').read_text().replace('transfer-deferred-count-flush-owned-floor-20261011-01','transfer-deferred-count-flush-owned-floor-20261011-02')
s=s.replace('Fresh finite step/arbitrary-walk framing and successful whole deferred-flush count/effect composition; all inherited proofs and guards unchanged.', 'Fresh successor removes unused simplification that changed reflexive queue equality into True. All three theorem conclusions and inherited guards unchanged; rejected whole attempt preserved with zero credit.')
(ROOT/'prepare.py').write_text(s)
f=ROOT/'handwritten/TransferDeferredCountFlush01.lean'; f.parent.mkdir()
lean=(PRIOR/'handwritten/TransferDeferredCountFlush01.lean').read_text()
before='    simp only [walked]\n'; assert lean.count(before)==1
f.write_text(lean.replace(before,''))
print({'fresh_audits':3,'rejected_predecessor_credit':0,'theorem_conclusions_unchanged':True})
