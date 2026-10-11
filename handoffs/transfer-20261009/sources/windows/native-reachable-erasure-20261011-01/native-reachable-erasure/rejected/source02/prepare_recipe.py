"""Fresh proof-only correction of implicit head membership arguments."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
old=DIAG/'transfer-native-reachable-erasure-20261011-01'
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
source=(old/'handwritten/TransferNativeReachableErasure01.lean').read_text()
assert source.count('(List.mem_cons_self request rest)')==1
source=source.replace('(List.mem_cons_self request rest)','List.mem_cons_self')
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferNativeReachableErasure01.lean').write_text(source)
s=(old/'prepare.py').read_text()
s=s.replace("POOL = DIAG / 'transfer-native-reachable-erasure-owned-floor-20261011-01'","POOL = DIAG / 'transfer-native-reachable-erasure-owned-floor-20261011-02'")
anchor="plan['pins'] += mapping['runtime_sources']";assert s.count(anchor)==1
extra="rejected_reachable=DIAG/'transfer-native-reachable-erasure-20261011-01'\nplan['pins'] += [pin(rejected_reachable/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferNativeReachableErasure01.lean','project/ShielddSecurity/TransferNativeReachableErasure01.lean','runs/01-TransferNativeReachableErasure01/stdout.txt']]\n"
s=s.replace(anchor,extra+anchor)
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Source01 invalid application of implicit List.mem_cons_self arguments and kernel heap-consumption failure, strict whole0. Source02 uses the existing implicitly bound head membership theorem; definitions/premises/conclusions, fixed heap, finite heartbeats and all physical/per-run guards unchanged. Failed original fully retained, no compiler/memory failure control credit.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':3,'failed_original_credit':0,'repair':'implicit head membership application','heap_guard_unchanged':True})
