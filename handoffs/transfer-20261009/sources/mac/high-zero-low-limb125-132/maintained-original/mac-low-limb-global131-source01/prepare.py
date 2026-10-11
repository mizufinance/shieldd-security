from pathlib import Path
import re
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work')
def require(ok,msg):
 if not ok:raise ValueError(msg)
def emit(dirname,name,t,names):
 S=W/dirname;require(not S.exists(),'new stage');S.mkdir();(S/'template.lean').write_text(t)
 g=(W/'mac-high-limb-global123-source02/generate.py').read_text().replace('CapturedHighLimbGlobal123',name)
 a=g.index('audits=');b=g.index('\nt+=',a);g=g[:a]+"audits=['ShielddSecurity."+name+".'+n for n in "+repr(names)+"]"+g[b:]
 (S/'generate.py').write_text(g);(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
t=(W/'mac-high-limb-global123-source02/template.lean').read_text().replace('import ShielddSecurity.CapturedNextGlobal118','import ShielddSecurity.CapturedHighZeroShared127').replace('CapturedRegistryHighLimb121','CapturedRegistryLowLimb130').replace('CapturedRegistryHighLimb120','CapturedRegistryLowLimb129').replace('import ShielddSecurity.HighBitMeaning122','import ShielddSecurity.LowBitMeaning128').replace('CapturedHighLimbGlobal123','CapturedLowLimbGlobal131').replace('CapturedNextGlobal118.completed','CapturedHighZeroShared127.completed').replace('(asset/2^128)','(LowBitMeaning128.low asset)').replace('(value/2^128)','(LowBitMeaning128.low value)')
a=t.index('theorem high_frame');b=t.index('theorem inside',a)
t=t[:a]+'''theorem low_frame (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position column : Nat) (lower : 1112≤column) (upper : column<1242) :
    CapturedHighZeroShared127.completed base initial next asset value epoch position column=base column := by
  exact (CapturedHighZeroShared127.early_frame _ initial next asset value epoch position column (by omega) (by omega)).trans
    ((CapturedRegistryHighLimb121.outside _ (asset/2^128) (value/2^128) column (Or.inr (by omega))).trans
      (FieldZeroSeed125.outside base 1110 (CapturedHighZeroShared127.difference asset value) column (Or.inr lower)))
'''+t[b:]
# Only generic seed/fixed-frame region has literal high window references.
a=t.index('theorem inside');b=t.index('theorem asset_bits',a);mid=t[a:b];mp={981:1112,1110:1242,983:1114,982:1113,127:128};mid=re.sub(r'\b(?:'+'|'.join(map(str,mp))+r')\b',lambda m:str(mp[int(m[0])]),mid).replace('high_frame','low_frame');t=t[:a]+mid+t[b:]
a=t.index('theorem asset_high');b=t.index('variable [CharP F p]',a)
t=t[:a]+'''theorem asset_low (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) :
    fieldBinary (CapturedRegistryLowLimb129.leftColumns.map (completed base initial next asset value epoch position))=
      (LowBitMeaning128.low asset:F) :=
  LowBitMeaning128.low_meaning _ 471 asset (asset_bits base initial next asset value epoch position)
theorem value_low (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) :
    fieldBinary (CapturedRegistryLowLimb129.rightColumns.map (completed base initial next asset value epoch position))=
      (LowBitMeaning128.low value:F) :=
  LowBitMeaning128.low_meaning _ 216 value (value_bits base initial next asset value epoch position)
theorem zero (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) (one : base 0=1) :
    completed base initial next asset value epoch position 0=1 :=
  CapturedHighLimbGlobal123.zero _ initial next asset value epoch position
    ((FieldZeroSeed125.outside _ _ _ 0 (Or.inl (by decide))).trans
      ((CapturedRegistryLowLimb130.outside base _ _ 0 (Or.inl (by decide))).trans one))
'''+t[b:]
t=t.replace('theorem high_assertions','theorem low_assertions').replace('(next asset value epoch position : Nat) (left : asset<2^255) (right : value<2^255) :','(next asset value epoch position : Nat) :').replace('(178893+index)) 130','(179026+index)) 131')
t=t.replace('(HighBitMeaning122.high_bound asset left) (HighBitMeaning122.high_bound value right)','(LowBitMeaning128.low_bound asset) (LowBitMeaning128.low_bound value)').replace('(asset_high base initial next asset value epoch position left)','(asset_low base initial next asset value epoch position)').replace('(value_high base initial next asset value epoch position right)','(value_low base initial next asset value epoch position)')
emit('mac-low-limb-global131-source01','CapturedLowLimbGlobal131',t,['completed','low_frame','inside','seeded_fixed','final_seeded','asset_bits','value_bits','asset_low','value_low','zero','arithmetic','low_assertions'])
old=(W/'mac-high-zero-shared127-source02/template.lean').read_text();a=old.index('theorem legal_registry_global1071');b=old.index(' := by',a);stmt=old[a:b].replace('legal_registry_global1071','legal_registry_global1202')
# Parenthesize complete old1071 result before new131 result.
c=stmt.index(' :\n    ((');stmt=stmt[:c]+stmt[c:].replace(' :\n    ((',' :\n    (((',1)+''') ∧
    SatisfiesAt (completed base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (179026+index)) 131'''
head='''import ShielddSecurity.CapturedLowLimbGlobal131
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedLowLimbShared132
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F]
abbrev completed := CapturedLowLimbGlobal131.completed (F:=F)
theorem claimed_seed (base : Nat → F) (asset value : Nat) (group : Fin 4) :
    CapturedFourSubgroupSeed89.Claimed (CapturedRegistryLowLimb130.seeded base (LowBitMeaning128.low asset) (LowBitMeaning128.low value)) group=
      CapturedFourSubgroupSeed89.Claimed base group := by
  have fourteen:=CapturedSubgroupFrame92.safe group 14 (by decide) (by decide)
  have fifteen:=CapturedSubgroupFrame92.safe group 15 (by decide) (by decide)
  change Group.Point.mk _ _=Group.Point.mk _ _
  rw [CapturedRegistryLowLimb130.outside base _ _ _ (Or.inl (Nat.lt_trans fourteen.2.2.2.2.2 (by decide))),
    CapturedRegistryLowLimb130.outside base _ _ _ (Or.inl (Nat.lt_trans fifteen.2.2.2.2.2 (by decide)))]
variable [CharP F p]
'''
body=''' := by
  have low (column : Nat) (bound : column<1112) :
      CapturedRegistryLowLimb130.seeded base (LowBitMeaning128.low w.asset) (LowBitMeaning128.low w.registry.value) column=base column :=
    CapturedRegistryLowLimb130.outside base _ _ column (Or.inl bound)
  have first:=CapturedHighZeroShared127.legal_registry_global1071 c w legal sinkMeaning
    (CapturedRegistryLowLimb130.seeded base (LowBitMeaning128.low w.asset) (LowBitMeaning128.low w.registry.value)) initial imaginary
    ((low 34 (by decide)).trans epoch) ((low 135 (by decide)).trans position)
    ((low 10 (by decide)).trans regulated) ((low 6 (by decide)).trans asset)
    ((low 11 (by decide)).trans registry)
    ((low 35 (by decide)).trans px) ((low 36 (by decide)).trans py)
    ((low 42 (by decide)).trans cx) ((low 43 (by decide)).trans cy)
    ((low 13 (by decide)).trans nextMeaning) ((low 0 (by decide)).trans zero)
    (fun group => (claimed_seed base w.asset w.registry.value group).trans (binding group))
    valid nonSquare imaginarySquare
  exact ⟨first,CapturedLowLimbGlobal131.low_assertions base initial
    w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position⟩
end ShielddSecurity.CapturedLowLimbShared132
'''
emit('mac-low-limb-shared132-source01','CapturedLowLimbShared132',head+stmt+body,['completed','claimed_seed','legal_registry_global1202'])
print('131/132 prepared; source-only')
