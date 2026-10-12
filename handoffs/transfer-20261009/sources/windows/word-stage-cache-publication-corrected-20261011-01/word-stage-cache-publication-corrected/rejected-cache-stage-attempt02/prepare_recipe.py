from pathlib import Path
ROOT=Path(__file__).resolve().parent
DIAG=ROOT.parent
OLD=DIAG/'transfer-word-stage-cache-publication-20261011-01'
assert not (ROOT/'prepare.py').exists()
s=(OLD/'prepare.py').read_text()
old="POOL = DIAG / 'transfer-word-stage-cache-publication-owned-floor-20261011-01'"
assert s.count(old)==1
s=s.replace(old,"POOL = DIAG / 'transfer-word-stage-cache-publication-owned-floor-20261011-02'")
anchor="plan['artifact_policy'] = "
at=s.index(anchor)
s=s[:at]+"failedCache=DIAG/'transfer-word-stage-cache-publication-20261011-01'\nplan['pins'] += [pin(failedCache/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordStageCachePublication01.lean','project/ShielddSecurity/TransferWordStageCachePublication01.lean','runs/01-TransferWordStageCachePublication01/stdout.txt']]\n"+s[at:]
source=(OLD/'handwritten/TransferWordStageCachePublication01.lean').read_text()
source=source.replace('  unfold stageAtKey at returned\n','  unfold stageAtKey at returned\n  simp only [Except.map] at returned\n')
source=source.replace('=> simp only [Except.map] at returned; cases returned','=> rw [staged] at returned; cases returned',1)
source=source.replace('  | ok result =>\n    cases result with','  | ok result =>\n    rw [staged] at returned\n    cases result with',1)
source=source.replace('    | error refusal => simp only [Except.map] at returned; cases returned','    | error refusal => cases returned',1)
source=source.replace('      exact ⟨object, rfl, exactCache.symm⟩','      exact ⟨object, staged, exactCache.symm⟩',1)
source=source.replace('  exact ⟨framed, congrArg (fun selected => match selected with | none => parent other | some value => value) framed⟩','  refine ⟨framed, ?_⟩\n  simp only [overlay, framed]',1)
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferWordStageCachePublication01.lean').write_text(source)
(ROOT/'prepare.py').write_text(s)
print({'fresh_source_proof_repair':True,'unchanged_definitions_contracts_and_guards':True,'failed_raw_files':10})
