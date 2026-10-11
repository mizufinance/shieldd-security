from pathlib import Path
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-registry-high-limb120-source01'
if S.exists():raise ValueError('immutable source')
t='''import ShielddSecurity.CapturedFullRelation58
import ShielddSecurity.CapturedAssertions50B0003
import ShielddSecurity.CapturedAssertions50B0004
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistryHighLimb120
open CompilerAssertionBlock51 CompilerArithmeticTransport41
noncomputable def columns : List Nat := List.range' 983 127
noncomputable def leftColumns : List Nat := List.range' 599 127
noncomputable def rightColumns : List Nat := List.range' 344 127
noncomputable def expected (index : Nat) : Recipe :=
  if index<128 then .square [(if index=0 then 981 else 982+index,1)] [(if index=0 then 981 else 982+index,1)]
  else if index=128 then .linear (weighted columns 1) [(982,1)]
  else .linear (weighted rightColumns 1++weighted leftColumns (-1)) [(982,1),(981,-(2^127))]
noncomputable def actual (index : Nat) : Option Row :=
  if index<85 then CapturedAssertions50B0003.block.actual (171+index)
  else CapturedAssertions50B0004.block.actual (index-85)
noncomputable def productionCheck : Bool := (List.range 130).all (fun index =>
  match actual index with
  | some row => checkRow p copy row (true,expected index)
  | none => false)
theorem production_checked : productionCheck=true := by decide +kernel
noncomputable def block : Block p copy 130 where
  actual := actual
  recipe := fun index => some (true,expected index)
  exact_checked := by
    intro index bound
    have h:=List.all_eq_true.mp production_checked index (List.mem_range.mpr bound)
    change (match actual index with | some row => checkRow p copy row (true,expected index) | none => false)=true at h
    cases found:actual index with
    | none => simp only [found] at h;contradiction
    | some row => exact ⟨row,(true,expected index),found,rfl,by simpa only [found] using h⟩
theorem hint_exact (index : Nat) (hint : Bool × Recipe) (found : block.recipe index=some hint) :
    hint.2=expected index := by
  change some (true,expected index)=some hint at found
  exact congrArg Prod.snd (Option.some.inj found).symm
theorem full_position (index : Nat) (bound : index<130) :
    CapturedFullRelation58.rowAt (178893+index)=block.actual index := by
  have sum : 178893+index=177954+(939+index) := by omega
  rw [sum,CapturedFullRelation58.assertion_position (939+index) (by omega)]
  have h12288 : 939+index<12288 := by omega
  have h4096 : 939+index<4096 := by omega
  have h2048 : 939+index<2048 := by omega
  change (if 939+index<12288 then _ else _) = _
  rw [if_pos h12288]
  change (if 939+index<4096 then _ else _) = _
  rw [if_pos h4096]
  change (if 939+index<2048 then _ else _) = _
  rw [if_pos h2048]
  change (if 939+index<1024 then _ else _) = _
  by_cases before : index<85
  · rw [if_pos (show 939+index<1024 by omega)]
    change (if 939+index<512 then _ else _) = _
    rw [if_neg (show ¬939+index<512 by omega)]
    change (if 939+index-512<256 then _ else _) = _
    rw [if_neg (show ¬939+index-512<256 by omega)]
    have same : 939+index-512-256=171+index := by omega
    change CapturedAssertions50B0003.block.actual (939+index-512-256)=
      (if index<85 then CapturedAssertions50B0003.block.actual (171+index)
        else CapturedAssertions50B0004.block.actual (index-85))
    rw [if_pos before,same]
  · rw [if_neg (show ¬939+index<1024 by omega)]
    change (if 939+index-1024<512 then _ else _) = _
    rw [if_pos (show 939+index-1024<512 by omega)]
    change (if 939+index-1024<256 then _ else _) = _
    rw [if_pos (show 939+index-1024<256 by omega)]
    have same : 939+index-1024=index-85 := by omega
    change CapturedAssertions50B0004.block.actual (939+index-1024)=
      (if index<85 then CapturedAssertions50B0003.block.actual (171+index)
        else CapturedAssertions50B0004.block.actual (index-85))
    rw [if_neg before,same]
end ShielddSecurity.CapturedRegistryHighLimb120
'''
S.mkdir();(S/'template.lean').write_text(t)
g=(W/'mac-next-canonical117-source01/generate.py').read_text();a=g.index('audits=');b=g.index('\nt+=',a)
g=g[:a]+"audits=['ShielddSecurity.CapturedRegistryHighLimb120.'+n for n in ['columns','leftColumns','rightColumns','expected','actual','productionCheck','production_checked','block','hint_exact','full_position']]"+g[b:]
g=g.replace('CapturedNextCanonical117','CapturedRegistryHighLimb120').replace('NextValue canonical two actual assertions178891/178892, independent n<p and actual arithmetic/bits; no shared constructor/fullTransfer conclusion.','First bounded limb130 actual assertion positions178893..179022: signed symbolic recipes canonically checked against actual outlined captured rows. No semantic truth/constructor/fullTransfer claim.')
(S/'generate.py').write_text(g);(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
