from pathlib import Path
import re
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work')
def require(ok,msg):
 if not ok:raise ValueError(msg)
def emit(dirname,name,t,names):
 S=W/dirname;require(not S.exists(),'fresh');S.mkdir();(S/'template.lean').write_text(t);g=(W/'mac-low-limb-global131-source01/generate.py').read_text().replace('CapturedLowLimbGlobal131',name);a=g.index('audits=');b=g.index('\nt+=',a);g=g[:a]+"audits=['ShielddSecurity."+name+".'+n for n in "+repr(names)+"]"+g[b:];(S/'generate.py').write_text(g);(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
t=(W/'mac-low-limb-global131-source01/template.lean').read_text().replace('CapturedRegistryLowLimb130','CapturedNextLowLimb141').replace('CapturedRegistryLowLimb129','CapturedNextLowLimb140').replace('CapturedLowLimbGlobal131','CapturedNextLowGlobal142').replace('import ShielddSecurity.CapturedHighZeroShared127','import ShielddSecurity.CapturedNextHighZeroShared139').replace('CapturedHighZeroShared127.completed','CapturedNextHighZeroShared139.completed').replace('(LowBitMeaning128.low asset) (LowBitMeaning128.low value)','(LowBitMeaning128.low next) (LowBitMeaning128.low asset)')
a=t.index('theorem low_frame');b=t.index('theorem inside',a);t=t[:a]+'''theorem low_frame (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position column : Nat) (lower : 1373≤column) (upper : column<1503) :
    CapturedNextHighZeroShared139.completed base initial next asset value epoch position column=base column := by
  exact (CapturedNextHighZeroShared139.early_frame _ initial next asset value epoch position column (by omega) (by omega)).trans
    ((CapturedNextHighLimb134.outside _ (next/2^128) (asset/2^128) column (Or.inr (by omega))).trans
      (FieldZeroSeed125.outside base 1371 (CapturedNextHighZeroShared139.difference next asset) column (Or.inr lower)))
'''+t[b:]
a=t.index('theorem inside');b=t.index('theorem asset_bits',a);mp={1112:1373,1113:1374,1114:1375,1242:1503};mid=re.sub(r'\b(?:'+'|'.join(map(str,mp))+r')\b',lambda m:str(mp[int(m[0])]),t[a:b]);t=t[:a]+mid+t[b:]
a=t.index('theorem asset_bits');b=t.index('variable [CharP F p]',a);t=t[:a]+'''theorem next_bits (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position index : Nat) (bound : index<255) :
    completed base initial next asset value epoch position (726+index)=
      if (encodeBits 255 next)[index]?.getD false then 1 else 0 := by
  exact (show _=BinaryComparison100.bit (F:=F) (CapturedValueComparison106.bitAt next (216+index)) from
    CapturedNextGlobal118.bits _ initial next asset value epoch position index bound).trans
      (by simp only [BinaryComparison100.bit,CapturedValueComparison106.bitAt,Nat.add_sub_cancel_left])
theorem asset_bits (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position index : Nat) (bound : index<255) :
    completed base initial next asset value epoch position (471+index)=
      if (encodeBits 255 asset)[index]?.getD false then 1 else 0 := by
  exact (show _=BinaryComparison100.bit (F:=F) (CapturedValueComparison106.bitAt asset (216+index)) from
    CapturedAssetGlobal113.bits _ initial asset value epoch position index bound).trans
      (by simp only [BinaryComparison100.bit,CapturedValueComparison106.bitAt,Nat.add_sub_cancel_left])
theorem next_low (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) :
    fieldBinary (CapturedNextLowLimb140.leftColumns.map (completed base initial next asset value epoch position))=
      (LowBitMeaning128.low next:F) :=
  LowBitMeaning128.low_meaning _ 726 next (next_bits base initial next asset value epoch position)
theorem asset_low (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) :
    fieldBinary (CapturedNextLowLimb140.rightColumns.map (completed base initial next asset value epoch position))=
      (LowBitMeaning128.low asset:F) :=
  LowBitMeaning128.low_meaning _ 471 asset (asset_bits base initial next asset value epoch position)
theorem zero (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) (one : base 0=1) :
    completed base initial next asset value epoch position 0=1 :=
  CapturedNextHighGlobal135.zero _ initial next asset value epoch position
    ((FieldZeroSeed125.outside _ _ _ 0 (Or.inl (by decide))).trans
      ((CapturedNextLowLimb141.outside base _ _ 0 (Or.inl (by decide))).trans one))
'''+t[b:]
t=t.replace('(179026+index)) 131','(179290+index)) 131').replace('(asset_low base initial next asset value epoch position)','(next_low base initial next asset value epoch position)').replace('(value_low base initial next asset value epoch position)','(asset_low base initial next asset value epoch position)').replace('(LowBitMeaning128.low_bound asset) (LowBitMeaning128.low_bound value)','(LowBitMeaning128.low_bound next) (LowBitMeaning128.low_bound asset)')
emit('mac-next-low-global142-source01','CapturedNextLowGlobal142',t,['completed','low_frame','inside','seeded_fixed','final_seeded','next_bits','asset_bits','next_low','asset_low','zero','arithmetic','low_assertions'])
t=(W/'mac-low-limb-shared132-source01/template.lean').read_text().replace('CapturedLowLimbGlobal131','CapturedNextLowGlobal142').replace('CapturedLowLimbShared132','CapturedNextLowShared143').replace('CapturedRegistryLowLimb130','CapturedNextLowLimb141').replace('theorem claimed_seed (base : Nat → F) (asset value : Nat)','theorem claimed_seed (base : Nat → F) (next asset : Nat)').replace('(LowBitMeaning128.low asset) (LowBitMeaning128.low value)','(LowBitMeaning128.low next) (LowBitMeaning128.low asset)')
a=t.index('theorem legal_registry_global1202');old=(W/'mac-next-high-zero-shared139-source02/template.lean').read_text();c=old.index('theorem legal_registry_global1335');d=old.index(' := by',c);stmt=old[c:d].replace('legal_registry_global1335','legal_registry_global1466');e=stmt.index(' :\n    ');stmt=stmt[:e]+stmt[e:].replace(' :\n    ',' :\n    (',1)+''') ∧
    SatisfiesAt (completed base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (179290+index)) 131'''
body=t[t.index(' := by',a):].replace('column<1112','column<1373').replace('(LowBitMeaning128.low w.asset) (LowBitMeaning128.low w.registry.value)','(LowBitMeaning128.low w.registry.nextValue) (LowBitMeaning128.low w.asset)').replace('CapturedHighZeroShared127.legal_registry_global1071','CapturedNextHighZeroShared139.legal_registry_global1335').replace('(claimed_seed base w.asset w.registry.value group)','(claimed_seed base w.registry.nextValue w.asset group)')
emit('mac-next-low-shared143-source01','CapturedNextLowShared143',t[:a]+stmt+body,['completed','claimed_seed','legal_registry_global1466'])
