"""Fresh proof-only overlay normalization successor; preserve all rejected bytes."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
PRIOR=DIAG/'transfer-deferred-count-walk-20261011-01'
assert not (ROOT/'prepare.py').exists()
events=[json.loads(x) for x in (PRIOR/'events.jsonl').read_text().splitlines()]
assert len(events)==2 and events[-1]['result']['status']=='failed'
s=(PRIOR/'prepare.py').read_text().replace('transfer-deferred-count-walk-owned-floor-20261011-01','transfer-deferred-count-walk-owned-floor-20261011-02')
s=s.replace(", ROOT / 'prepare-rejected-owned-count.py', ROOT / 'prepare_recipe-rejected-owned-count.py'", "")
s=s.replace('Fresh symbolic arbitrary-list deferred count recurrence on exact merged qualified closures; all inherited proofs and guards unchanged.', 'Fresh successor unfolds the overlay before the existing count-write rewrite. One definition and three theorem conclusions unchanged; rejected predecessor and pre-admission census repair preserved with zero credit.')
(ROOT/'prepare.py').write_text(s)
f=ROOT/'handwritten/TransferDeferredCountWalk01.lean'; f.parent.mkdir()
lean=(PRIOR/'handwritten/TransferDeferredCountWalk01.lean').read_text()
before='      rw [writeIndex_count]'; assert lean.count(before)==1
lean=lean.replace(before,'      simp only [overlay, writeIndex_count]')
f.write_text(lean)
print({'fresh_audits':4,'rejected_predecessor_credit':0,'definition_and_theorem_conclusions_unchanged':True})
