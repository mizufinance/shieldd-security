"""Fresh successor: proof-only repairs, rejected predecessor remains immutable."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
DIAG=ROOT.parent
PRIOR=DIAG/'transfer-index-count-codec-20261011-01'
assert not (ROOT/'prepare.py').exists()
events=[json.loads(x) for x in (PRIOR/'events.jsonl').read_text().splitlines()]
assert len(events)==2 and events[-1]['result']['status']=='failed'
s=(PRIOR/'prepare.py').read_text().replace('transfer-index-count-codec-owned-floor-20261011-01','transfer-index-count-codec-owned-floor-20261011-02')
s=s.replace('Fresh symbolic width lemmas instantiate the mathematical u64 index-count codec through the qualified current-overlay/whole Ordinary count closure.', 'Fresh successor repairs reserved branch binder, product orientation and typed dependent-if refusal proof. Five codec definitions and ten theorem conclusions unchanged. Rejected predecessor preserved with zero credit.')
(ROOT/'prepare.py').write_text(s)
f=ROOT/'handwritten/TransferIndexCountCodec01.lean'; f.parent.mkdir()
lean=(PRIOR/'handwritten/TransferIndexCountCodec01.lean').read_text()
assert lean.count('by simpa only [Nat.pow_succ] using bounded')==1
lean=lean.replace('by simpa only [Nat.pow_succ] using bounded','by simpa only [Nat.pow_succ\'] using bounded')
lean=lean.replace('next unsafe =>','next rejected =>').replace('unsafe ⟨','rejected ⟨')
before='  simp only [decodeCount, if_neg (fun safe => wrong safe.1)]'
assert lean.count(before)==1
lean=lean.replace(before,'  have rejected : ¬ (bytes.length = 8 ∧ validBytes bytes = true ∧ decodeBE bytes < 2 ^ 64) := fun safe => wrong safe.1\n  simp only [decodeCount, dif_neg rejected]')
f.write_text(lean)
print({'fresh_audits':15,'rejected_predecessor_credit':0,'definitions_and_conclusions_unchanged':True})
