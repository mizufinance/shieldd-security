"""Fresh proof repair: avoid multiline record-update parser ambiguity."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
old=DIAG/'transfer-native-ghost-erasure-20261011-01'
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
source=(old/'handwritten/TransferNativeGhostErasure01.lean').read_text()
start=source.index('  change (match raw.currentSource child with')
end=source.index('\ntheorem bounded_raw_transfer_',start)
source=source[:start]+'''  cases source : raw.currentSource child with
  | none => simp only [TransferRawEffectsSource01.reshape, nativeRaw, nativeOnlyRaw, source]
  | some sourceHasId =>
    have primitive := bounded_primitive_ghost_erasure_preserves_every_returned_outcome
      encodeNative raw wordMax objectKey sourceHasId child inputs initial bounded nativeInputs belowWord
    have extendedSource : (nativeRaw encodeNative raw).currentSource child = some sourceHasId := source
    have onlySource : (nativeOnlyRaw encodeNative raw).currentSource child = some sourceHasId := source
    simp only [TransferRawEffectsSource01.reshape, extendedSource, onlySource]
    rw [primitive]
    cases observed : executeNullify (nativeOnlyRaw encodeNative raw).nullifiers wordMax blockCapacity objectKey sourceHasId child inputs with
    | mk cache result =>
      cases result with
      | error error => rfl
      | ok returnedUnit =>
        cases returnedUnit
        exact notes_ignore_the_erased_nullifier_encoder encodeNative raw sourceHasId
          {child with cache := TransferRawEffectsSource01.emitSpends raw.spentEvent cache inputs} outputs

'''+source[end:]
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferNativeGhostErasure01.lean').write_text(source)
s=(old/'prepare.py').read_text()
s=s.replace("POOL = DIAG / 'transfer-native-ghost-erasure-owned-floor-20261011-01'","POOL = DIAG / 'transfer-native-ghost-erasure-owned-floor-20261011-02'")
anchor="plan['pins'] += mapping['runtime_sources']";assert s.count(anchor)==1
extra="rejected_erasure=DIAG/'transfer-native-ghost-erasure-20261011-01'\nplan['pins'] += [pin(rejected_erasure/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferNativeGhostErasure01.lean','project/ShielddSecurity/TransferNativeGhostErasure01.lean','runs/01-TransferNativeGhostErasure01/stdout.txt']]\n"
s=s.replace(anchor,extra+anchor)
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Source01 parser ambiguity in multiline cache record update, strict whole0. Source02 proof-only rewrite follows exact common current-source and primitive outcome cases, with one-line cache update; all definitions, theorem premises/conclusions and physical/per-run guards unchanged. Failed original retained completely.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':5,'failed_original_credit':0,'repair':'source/primitive exact outcome cases'})
