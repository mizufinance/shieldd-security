from pathlib import Path
import re
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-next-canonical117-source01';A=W/'mac-asset-canonical112-source01'
if S.exists():raise ValueError('immutable canonical')
S.mkdir();t=(A/'template.lean').read_text().replace('CapturedAssetCanonical112','CapturedNextCanonical117').replace('AssetComparison111','NextComparison116').replace('CapturedRegistryAssetRange109','CapturedRegistryNextRange114').replace('CapturedAssertions50B0002','CapturedAssertions50B0003');nums={471:726,725:980,33260:33768,178633:178891,167:169}
t=re.sub(r'\b(?:'+'|'.join(map(str,nums))+r')\b',lambda m:str(nums[int(m[0])]),t)
a=t.index('theorem full_position');b=t.index('variable {F',a)
t=t[:a]+'''theorem full_position (index : Nat) (bound : index<2) :
    CapturedFullRelation58.rowAt (178891+index)=block.actual index := by
  have sum : 178891+index=177954+(937+index) := by omega
  rw [sum,CapturedFullRelation58.assertion_position (937+index) (by omega)]
  have h12288 : 937+index<12288 := by omega
  have h4096 : 937+index<4096 := by omega
  have h2048 : 937+index<2048 := by omega
  have h1024 : 937+index<1024 := by omega
  change (if 937+index<12288 then _ else _) = _
  rw [if_pos h12288]
  change (if 937+index<4096 then _ else _) = _
  rw [if_pos h4096]
  change (if 937+index<2048 then _ else _) = _
  rw [if_pos h2048]
  change (if 937+index<1024 then _ else _) = _
  rw [if_pos h1024]
  change (if 937+index<512 then _ else _) = _
  rw [if_neg (show ¬937+index<512 by omega)]
  change (if 937+index-512<256 then CapturedAssertions50B0002.block.actual (937+index-512)
    else CapturedAssertions50B0003.block.actual (937+index-512-256)) = CapturedAssertions50B0003.block.actual (169+index)
  have same : 937+index-512-256=169+index := by omega
  rw [if_neg (show ¬937+index-512<256 by omega),same]
'''+t[b:];(S/'template.lean').write_text(t)
g=(A/'generate.py').read_text().replace('CapturedAssetCanonical112','CapturedNextCanonical117').replace('Asset canonical two actual assertions178633/178634','NextValue canonical two actual assertions178891/178892');(S/'generate.py').write_text(g);(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
