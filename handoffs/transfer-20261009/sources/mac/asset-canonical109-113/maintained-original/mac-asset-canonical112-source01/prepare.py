from pathlib import Path
import json,hashlib,re
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-asset-canonical112-source01';old=W/'mac-value-canonical107-source02/template.lean'
if S.exists():raise ValueError('immutable source')
S.mkdir();t=old.read_text();t=t[:t.index('\nset_option pp.all true in\n#check')]
t=t.replace('import ShielddSecurity.CapturedValueComparison106','import ShielddSecurity.AssetComparison111').replace('import ShielddSecurity.CapturedRegistryValueRange97','import ShielddSecurity.CapturedRegistryAssetRange109').replace('CapturedValueCanonical107','CapturedAssetCanonical112').replace('CapturedValueComparison106.semantic','AssetComparison111.canonical_value')
nums={470:725,32752:33260,178375:178633,165:167,216:471}
t=re.sub(r'\b(?:'+'|'.join(map(str,nums))+r')\b',lambda m:str(nums[int(m[0])]),t)
t=t.replace('CapturedValueComparison106.bitAt n (471+index)','CapturedValueComparison106.bitAt n (216+index)')
# The two canonical rows are in assertion provider2, indices167 and168.
t=t.replace('CapturedAssertions50B0001.block.actual (167+index)','CapturedAssertions50B0002.block.actual (167+index)').replace('CapturedAssertions50B0001.block.recipe (167+index)','CapturedAssertions50B0002.block.recipe (167+index)').replace('CapturedAssertions50B0001.block.exact_checked (167+index)','CapturedAssertions50B0002.block.exact_checked (167+index)')
a=t.index('theorem full_position');z=t.index('variable {F',a)
t=t[:a]+'''theorem full_position (index : Nat) (bound : index<2) :
    CapturedFullRelation58.rowAt (178633+index)=block.actual index := by
  have sum : 178633+index=177954+(679+index) := by omega
  rw [sum,CapturedFullRelation58.assertion_position (679+index) (by omega)]
  have h12288 : 679+index<12288 := by omega
  have h4096 : 679+index<4096 := by omega
  have h2048 : 679+index<2048 := by omega
  have h1024 : 679+index<1024 := by omega
  change (if 679+index<12288 then _ else _) = _
  rw [if_pos h12288]
  change (if 679+index<4096 then _ else _) = _
  rw [if_pos h4096]
  change (if 679+index<2048 then _ else _) = _
  rw [if_pos h2048]
  change (if 679+index<1024 then _ else _) = _
  rw [if_pos h1024]
  change (if 679+index<512 then _ else _) = _
  rw [if_neg (show ¬679+index<512 by omega)]
  change (if 679+index-512<256 then CapturedAssertions50B0002.block.actual (679+index-512)
    else CapturedAssertions50B0003.block.actual (679+index-512-256)) = CapturedAssertions50B0002.block.actual (167+index)
  have same : 679+index-512=167+index := by omega
  rw [if_pos (show 679+index-512<256 by omega),same]
''' +t[z:]
(S/'template.lean').write_text(t)
# Generic immutable emitter; this owned generator has exact declared audit census.
g=(W/'mac-asset-comparison111-root-source01/generate.py').read_text();g=g.replace("audits=['ShielddSecurity.AssetComparison111.pullback_satisfies','ShielddSecurity.AssetComparison111.canonical_value']","audits=['ShielddSecurity.CapturedAssetCanonical112.'+n for n in ['valueLC','expected','block','hint_exact','full_position','value_one','truth','complete']]").replace("p=r/'AssetComparison111.lean'","p=r/'CapturedAssetCanonical112.lean'").replace("name='AssetComparison111'","name='CapturedAssetCanonical112'").replace('Only actual asset508 arithmetic row transport and independent numeric canonical conclusion; no canonical assertion/shared constructor claimed.','Asset canonical two actual assertions178633/178634, independent n<p and actual arithmetic/bits; no shared constructor/fullTransfer conclusion.')
(S/'generate.py').write_text(g);(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'source-correspondence01.json').write_text(json.dumps({'original':str(old),'sha256':hashlib.sha256(old.read_bytes()).hexdigest(),'source_only':True},sort_keys=True)+'\n')
