from pathlib import Path
import re,json,hashlib
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-registry-next-range114-source01';A=W/'mac-registry-asset-range109-source02'
if S.exists():raise ValueError('immutable source')
S.mkdir();mods={'CapturedRegistryAssetRange109Data':'CapturedRegistryNextRange114Data','CapturedRegistryAssetRange109':'CapturedRegistryNextRange114','CapturedAssertions50B0001':'CapturedAssertions50B0002','CapturedAssertions50B0002':'CapturedAssertions50B0003'};nums={471:726,726:981,6:13,89:87,167:169,178377:178635,178633:178891}
def tr(t):
 t=re.sub(r'\b(?:'+'|'.join(mods)+r')\b',lambda m:mods[m[0]],t)
 return re.sub(r'\b(?:'+'|'.join(map(str,nums))+r')\b',lambda m:str(nums[int(m[0])]),t)
for n in ['data-template.lean','proof-template.lean']:
 t=tr((A/n).read_text())
 if n=='proof-template.lean':
  a=t.index('theorem full_position');b=t.index('theorem full_complete',a)
  t=t[:a]+'''theorem full_position (index : Nat) (bound : index<256) :
    CapturedFullRelation58.rowAt (178635+index)=block.actual index := by
  have sum : 178635+index=177954+(681+index) := by omega
  rw [sum,CapturedFullRelation58.assertion_position (681+index) (by omega)]
  have h12288 : 681+index<12288 := by omega
  have h4096 : 681+index<4096 := by omega
  have h2048 : 681+index<2048 := by omega
  have h1024 : 681+index<1024 := by omega
  change (if 681+index<12288 then _ else _) = _
  rw [if_pos h12288]
  change (if 681+index<4096 then _ else _) = _
  rw [if_pos h4096]
  change (if 681+index<2048 then _ else _) = _
  rw [if_pos h2048]
  change (if 681+index<1024 then _ else _) = _
  rw [if_pos h1024]
  change (if 681+index<512 then _ else _) = _
  rw [if_neg (show ¬681+index<512 by omega)]
  change (if 681+index-512<256 then CapturedAssertions50B0002.block.actual (681+index-512)
    else CapturedAssertions50B0003.block.actual (681+index-512-256)) =
    (if index<87 then CapturedAssertions50B0002.block.actual (169+index)
      else CapturedAssertions50B0003.block.actual (index-87))
  by_cases before : index<87
  · have h256 : 681+index-512<256 := by omega
    have same : 681+index-512=169+index := by omega
    rw [if_pos h256,if_pos before,same]
  · have h256 : ¬681+index-512<256 := by omega
    have same : 681+index-512-256=index-87 := by omega
    rw [if_neg h256,if_neg before,same]

'''+t[b:]
 (S/n).write_text(t)
g=tr((A/'generate.py').read_text());g=g.replace('Asset255bit range and reconstructed original column6, actual positions178377..178632','NextValue255bit range and reconstructed original column13, actual positions178635..178890');(S/'generate.py').write_text(g)
(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'source-correspondence01.json').write_text(json.dumps({'original':str(A),'parameters':nums,'source_only':True,'formal_credit':0},sort_keys=True)+'\n')
