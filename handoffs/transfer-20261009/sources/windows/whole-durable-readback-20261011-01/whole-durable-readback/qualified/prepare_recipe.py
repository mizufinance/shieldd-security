"""Proof-only fresh successor for dependent cases and explicit Status binder."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
ORIGINAL=DIAG/'transfer-whole-durable-readback-20261011-01'
assert not (ROOT/'prepare.py').exists()
source=(ORIGINAL/'handwritten/TransferWholeDurableReadback01.lean').read_text()
assert source.count('exact ⟨store, boundary, response, reader, boundaryRead, locked, checked, unspent⟩')==1
source=source.replace('exact ⟨store, boundary, response, reader, boundaryRead, locked, checked, unspent⟩',
    'exact ⟨store, boundary, response, rfl, rfl, rfl, checked, unspent⟩')
assert source.count('∃ store boundary response,')==3
source=source.replace('∃ store boundary response,','∃ (store : Store) (boundary : Boundary) (response : Status),')
handwritten=ROOT/'handwritten/TransferWholeDurableReadback01.lean'
handwritten.parent.mkdir(parents=True)
handwritten.write_text(source)
s=(ORIGINAL/'prepare.py').read_text()
s=s.replace('transfer-whole-durable-readback-owned-floor-20261011-01','transfer-whole-durable-readback-owned-floor-20261011-02')
needle="plan['pins'] += mapping['runtime_sources']"
assert s.count(needle)==1
s=s.replace(needle,"""rejected_durable = DIAG / 'transfer-whole-durable-readback-20261011-01'
plan['pins'] += [pin(rejected_durable / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py',
    'source-mapping.json', 'events.jsonl', 'handwritten/TransferWholeDurableReadback01.lean',
    'project/ShielddSecurity/TransferWholeDurableReadback01.lean', 'runs/01-TransferWholeDurableReadback01/stdout.txt']]
"""+needle)
s=s.replace("plan['source_repairs'] = 'Fresh current Reader/boundary/lock/verified status installation and whole-delivery semantic absence composition; exact old Readback source/object/17 full reports reused without replay; guards unchanged.'", "plan['source_repairs'] = 'Fresh successor changes only dependent case goal evidence to reflexivity and adds explicit Store/Boundary/Status existential annotations to the intended types. All semantic premises/conclusions remain unchanged; failed predecessor retained with zero credit; guards unchanged.'")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':11,'inherited_audits':368,'owned_modules':37,'failed_predecessors':1})
