from pathlib import Path
import re
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-next-global118-source01'
if S.exists():raise ValueError('immutable source')
old=(W/'mac-asset-global113-source02/template.lean').read_text();a=old.index('theorem legal_registry_global680');b=old.index(' := by\n',a)
t=old[:a].replace('import ShielddSecurity.CapturedAssetCanonical112','import ShielddSecurity.CapturedNextCanonical117').replace('import ShielddSecurity.CapturedValueGlobal108','import ShielddSecurity.CapturedAssetGlobal113').replace('CapturedAssetGlobal113','CapturedNextGlobal118').replace('CapturedRegistryAssetRange109','CapturedRegistryNextRange114').replace('CapturedAssetCanonical112','CapturedNextCanonical117')
t=re.sub(r'\basset\b','next',t).replace('(next value epoch position','(next asset value epoch position').replace('base initial next value epoch position','base initial next asset value epoch position')
t=t.replace('CapturedValueGlobal108.completed (CapturedRegistryNextRange114.completed base next) initial value epoch position','CapturedAssetGlobal113.completed (CapturedRegistryNextRange114.completed base next) initial asset value epoch position')
t=t.replace('471','726').replace('178377','178635').replace('178633','178891')
t=t.replace('CapturedRegistryValueRange97.completed (CapturedRegistryNextRange114.completed base next) value','CapturedRegistryValueRange97.completed (CapturedRegistryAssetRange109.completed (CapturedRegistryNextRange114.completed base next) asset) value')
t=t.replace('exact a.trans (CapturedRegistryValueRange97.completed_outside _ value (726+index) (Or.inr (by omega)))','exact a.trans ((CapturedRegistryValueRange97.completed_outside _ value (726+index) (Or.inr (by omega))).trans\n    (CapturedRegistryAssetRange109.completed_outside _ asset (726+index) (Or.inr (by omega))))')
t=t.replace('theorem six_frame','theorem thirteen_frame').replace('completed base initial next asset value epoch position 6=base 6','completed base initial next asset value epoch position 13=base 13').replace('epoch position 6 (by decide)','epoch position 13 (by decide)').replace('outside _ value 6 (Or.inl (by decide))','outside _ value 13 (Or.inl (by decide))')
t=t.replace('(CapturedRegistryNextRange114.completed_fixed base next).2.2.2.2)', '((CapturedRegistryAssetRange109.completed_outside _ asset 13 (Or.inl (by decide))).trans\n        (CapturedRegistryNextRange114.completed_fixed base next).2.2.2.2))')
t=t.replace('CapturedValueGlobal108.zero _ initial value epoch position','CapturedAssetGlobal113.zero _ initial asset value epoch position').replace('rw [same,six_frame]','rw [same,thirteen_frame]')
# Every dependent use keeps one final assignment, seeded before arithmetic.
header=old[a:b].replace('legal_registry_global680','legal_registry_global938').replace('completed base initial w.asset','completed base initial w.registry.nextValue w.asset')
header=header.replace('(zero : base 0=1)','(nextMeaning : base 13=(w.registry.nextValue:F))\n    (zero : base 0=1)')
header+=''' ∧
    SatisfiesAt (completed base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (178635+index)) 256 ∧
    SatisfiesAt (completed base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (178891+index)) 2 := by
  have low (column : Nat) (bound : column<726) : CapturedRegistryNextRange114.completed base w.registry.nextValue column=base column :=
    CapturedRegistryNextRange114.completed_outside base _ column (Or.inl bound)
  have first:=CapturedAssetGlobal113.legal_registry_global680 c w legal sinkMeaning
    (CapturedRegistryNextRange114.completed base w.registry.nextValue) initial imaginary
    ((low 34 (by decide)).trans epoch) ((low 135 (by decide)).trans position)
    ((low 10 (by decide)).trans regulated) ((low 6 (by decide)).trans asset)
    ((low 11 (by decide)).trans registry)
    ((low 35 (by decide)).trans px) ((low 36 (by decide)).trans py)
    ((low 42 (by decide)).trans cx) ((low 43 (by decide)).trans cy)
    ((low 0 (by decide)).trans zero)
    (fun group => (claimed_seed base w.registry.nextValue group).trans (binding group))
    valid nonSquare imaginarySquare
  have nextBound : w.registry.nextValue<p := legal.2.2.2.2.2.2.2.2.1
  exact ⟨first.1,first.2.1,first.2.2.1,first.2.2.2.1,first.2.2.2.2.1,first.2.2.2.2.2.1,first.2.2.2.2.2.2,
    range_assertions base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position
      (Nat.lt_trans nextBound CapturedRegistryValueFrame98.modulus_bound) nextMeaning,
    canonical_assertions base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position nextBound zero⟩
end ShielddSecurity.CapturedNextGlobal118
'''
t+=header
S.mkdir();(S/'template.lean').write_text(t)
g=(W/'mac-asset-global113-source02/generate.py').read_text().replace('CapturedAssetGlobal113','CapturedNextGlobal118').replace('six_frame','thirteen_frame').replace('legal_registry_global680','legal_registry_global938').replace('680 distinct','938 distinct')
(S/'generate.py').write_text(g);(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
print(len(t.encode()))
