"""Fresh proof-only repair; preserve both withdrawn and failed originals."""
from pathlib import Path
ROOT = Path(__file__).resolve().parent
old = ROOT.parent / 'transfer-native-seal-transfer-20261011-02'
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
source = (old/'handwritten/TransferNativeSealTransfer01.lean').read_text()
a = '''    (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project state).objects _ = _ at stored'''
b = '''    (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project state).objects (project TransferNullifierObjectKeys01.nullifierBytes) =
      some (TransferPendingFiniteCodec01.encode (encodeObject encodeNative)
        (TransferPendingSealSource01.freeze (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project state))) at stored'''
assert source.count(a) == 1
source = source.replace(a,b)
assert source.count('∃ frozen, frozen.insertions.accepted') == 1
source = source.replace('∃ frozen, frozen.insertions.accepted','∃ (frozen : TransferWriterPrepareSource01.Frozen), frozen.insertions.accepted')
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferNativeSealTransfer01.lean').write_text(source)
s = (old/'prepare.py').read_text()
s = s.replace("POOL = DIAG / 'transfer-native-seal-transfer-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-native-seal-transfer-owned-floor-20261011-03'")
anchor = "plan['pins'] += mapping['runtime_sources']"
assert s.count(anchor) == 1
extra = "rejected_native_seal = DIAG/'transfer-native-seal-transfer-20261011-02'\nplan['pins'] += [pin(rejected_native_seal/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferNativeSealTransfer01.lean','project/ShielddSecurity/TransferNativeSealTransfer01.lean','runs/01-TransferNativeSealTransfer01/stdout.txt']]\n"
s = s.replace(anchor,extra+anchor)
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Source01 UNRUN withdrawn, source02 strict failed with zero whole-proof credit; source03 specifies the Unit-normalized current-pending rewrite RHS and the already intended Frozen existential type. Proof-only elaboration repairs preserve source02 reached-state finalization/supported-native getter premises and conclusions. Frozen originals retained; physical and per-run guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_proofs':3,'failed_original_credit':0,'repair':'explicit current-pending RHS and Frozen binder'})
