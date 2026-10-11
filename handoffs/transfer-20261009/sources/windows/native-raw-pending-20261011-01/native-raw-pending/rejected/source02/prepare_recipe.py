"""Fresh proof-only repairs for explicit sum type and exact primitive receipt."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
old=DIAG/'transfer-native-raw-pending-20261011-01'
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
source=(old/'handwritten/TransferNativeRawPending01.lean').read_text()
a='(fun native => .inl (encodeNative native))'
assert source.count(a)==1
source=source.replace(a,'(fun native => (Sum.inl (encodeNative native) : ExtendedObject O))')
start=source.index('  simpa only [TransferRawEffectsSource01.reshape, TransferRawSourceFrames01.installNotes,')
end=source.index('\n\nset_option pp.all',start)
source=source[:start]+'''  have reshaped := TransferRawEffectsSource01.successful_nullify_emits_all_spends_before_notes
    (TransferRawSourceFrames01.installNotes (nativeRaw encodeNative raw) notes sct treeKey notesKey)
    wordMax blockCapacity pendingKey child inputs outputs sourceHasId cache source passed
  rw [reshaped]
  exact framed.trans staged
'''+source[end:]
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferNativeRawPending01.lean').write_text(source)
s=(old/'prepare.py').read_text()
s=s.replace("POOL = DIAG / 'transfer-native-raw-pending-owned-floor-20261011-01'","POOL = DIAG / 'transfer-native-raw-pending-owned-floor-20261011-02'")
anchor="plan['pins'] += mapping['runtime_sources']";assert s.count(anchor)==1
extra="rejected_native_raw=DIAG/'transfer-native-raw-pending-20261011-01'\nplan['pins'] += [pin(rejected_native_raw/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferNativeRawPending01.lean','project/ShielddSecurity/TransferNativeRawPending01.lean','runs/01-TransferNativeRawPending01/stdout.txt']]\n"
s=s.replace(anchor,extra+anchor)
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Source01 strict failed with zero whole-proof credit. Source02 proof-only repairs give Sum.inl its explicit ExtendedObject result type and rewrite the exact original successful-nullify receipt before projecting returned raw cache. Definitions, theorem premises/conclusions and physical/per-run guards unchanged. Failed original fully retained.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':3,'failed_original_credit':0,'repair':'explicit sum type and original reshape receipt'})
