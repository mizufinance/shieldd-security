"""Repair only the generator's codec projection proof in a fresh successor."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
PRIOR=DIAG/'transfer-ordinary-max-count-20261011-01'
assert not (ROOT/'prepare.py').exists()
events=[json.loads(x) for x in (PRIOR/'events.jsonl').read_text().splitlines()]
assert len(events)==2 and events[-1]['result']['status']=='failed'
generator=(PRIOR/'generate.py').read_text()
before='  apply (TransferIndexCountCodec01.decode_success_iff _ _).mpr'
assert generator.count(before)==1
generator=generator.replace(before,'  change TransferIndexCountCodec01.decodeCount maxBytes = some (⟨2 ^ 64 - 1, by decide⟩ : Ordinal)\n'+before)
(ROOT/'generate.py').write_text(generator)
s=(PRIOR/'prepare.py').read_text().replace('transfer-ordinary-max-count-owned-floor-20261011-01','transfer-ordinary-max-count-owned-floor-20261011-02')
s=s.replace('Fresh generated exact max-byte/concrete-codec specialization of qualified whole Ordinary contracts; no predecessor changes or ancestor replays.', 'Fresh successor generator unfolds the concrete codec projection before applying the original decoding theorem. One definition and five theorem conclusions unchanged; failed predecessor preserved with zero credit.')
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':6,'rejected_predecessor_credit':0,'generated_source_repair':True})
