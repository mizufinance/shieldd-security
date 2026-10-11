from pathlib import Path
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');old=W/'mac-next-high-limb133-source01';S=W/'mac-next-high-limb133-source02'
def require(ok,msg):
 if not ok:raise ValueError(msg)
require(not S.exists(),'fresh');S.mkdir();t=(old/'template.lean').read_text().replace('import ShielddSecurity.CapturedAssertions50B0004','import ShielddSecurity.CapturedAssertions50B0004\nimport ShielddSecurity.CapturedAssertions50B0005')
t=t.replace('  CapturedAssertions50B0004.block.actual (179+index)','  if index<77 then CapturedAssertions50B0004.block.actual (179+index)\n  else CapturedAssertions50B0005.block.actual (index-77)',1)
a=t.index('  change (if 1203+index-1024<256');t=t[:a]+'''  change (if 1203+index-1024<256 then _ else _) = _
  by_cases before : index<77
  · rw [if_pos (show 1203+index-1024<256 by omega)]
    have same : 1203+index-1024=179+index := by omega
    change CapturedAssertions50B0004.block.actual (1203+index-1024)=
      (if index<77 then CapturedAssertions50B0004.block.actual (179+index)
        else CapturedAssertions50B0005.block.actual (index-77))
    rw [if_pos before,same]
  · rw [if_neg (show ¬1203+index-1024<256 by omega)]
    have same : 1203+index-1024-256=index-77 := by omega
    change CapturedAssertions50B0005.block.actual (1203+index-1024-256)=
      (if index<77 then CapturedAssertions50B0004.block.actual (179+index)
        else CapturedAssertions50B0005.block.actual (index-77))
    rw [if_neg before,same]
end ShielddSecurity.CapturedNextHighLimb133
''';(S/'template.lean').write_text(t);(S/'generate.py').write_bytes((old/'generate.py').read_bytes());(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
