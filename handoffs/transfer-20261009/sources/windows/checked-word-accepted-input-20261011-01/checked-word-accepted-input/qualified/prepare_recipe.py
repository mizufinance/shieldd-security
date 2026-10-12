from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-checked-word-accepted-input-20261011-01'
assert not (ROOT/'prepare.py').exists()
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-checked-word-accepted-input-owned-floor-20261011-01'","POOL = DIAG / 'transfer-checked-word-accepted-input-owned-floor-20261011-02'")
at=s.index("plan['artifact_policy'] = ")
s=s[:at]+"failedAccepted=DIAG/'transfer-checked-word-accepted-input-20261011-01'\nplan['pins'] += [pin(failedAccepted/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/checked-word-accepted-source-shape.json','handwritten/TransferCheckedWordAcceptedInput01.lean','project/ShielddSecurity/TransferCheckedWordAcceptedInput01.lean','runs/01-TransferCheckedWordAcceptedInput01/stdout.txt']]\n"+s[at:]
source=(OLD/'handwritten/TransferCheckedWordAcceptedInput01.lean').read_text()
old='  exact ⟨width, TransferScalarLittleEndianBytes01.fixed_four_word_source_scalar_projection_is_canonical scalar.words,\n    TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value scalar.words⟩'
assert source.count(old)==1
source=source.replace(old,'  have canonical := TransferScalarLittleEndianBytes01.fixed_four_word_source_scalar_projection_is_canonical scalar.words\n  have value := TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value scalar.words\n  unfold scalarKey at canonical value\n  exact ⟨width, canonical, value⟩')
(ROOT/'handwritten').mkdir();(ROOT/'context').mkdir()
(ROOT/'handwritten/TransferCheckedWordAcceptedInput01.lean').write_text(source)
(ROOT/'context/checked-word-accepted-source-shape.json').write_bytes((OLD/'context/checked-word-accepted-source-shape.json').read_bytes())
(ROOT/'prepare.py').write_text(s)
print({'scalar_key_alias_unfolding_only':True,'finite_heartbeats_unchanged':True,'failed_raw_files':11,'same_definitions_contracts_guards':True})
