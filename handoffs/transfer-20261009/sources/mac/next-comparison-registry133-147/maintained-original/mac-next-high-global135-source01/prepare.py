from pathlib import Path
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work')
def require(ok,msg):
 if not ok:raise ValueError(msg)
def emit(dirname,name,t,names):
 S=W/dirname;require(not S.exists(),'fresh');S.mkdir();(S/'template.lean').write_text(t);g=(W/'mac-low-limb-global131-source01/generate.py').read_text().replace('CapturedLowLimbGlobal131',name);a=g.index('audits=');b=g.index('\nt+=',a);g=g[:a]+"audits=['ShielddSecurity."+name+".'+n for n in "+repr(names)+"]"+g[b:];(S/'generate.py').write_text(g);(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
t=(W/'mac-high-limb-global123-source02/template.lean').read_text().replace('import ShielddSecurity.CapturedNextGlobal118','import ShielddSecurity.CapturedLowLimbShared132').replace('CapturedRegistryHighLimb121','CapturedNextHighLimb134').replace('CapturedRegistryHighLimb120','CapturedNextHighLimb133').replace('CapturedHighLimbGlobal123','CapturedNextHighGlobal135').replace('CapturedNextGlobal118.completed','CapturedLowLimbShared132.completed')
t=t.replace('(asset/2^128) (value/2^128)','(next/2^128) (asset/2^128)')
a=t.index('theorem high_frame');b=t.index('theorem inside',a);t=t[:a]+'''theorem high_frame (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position column : Nat) (lower : 1242≤column) (upper : column<1371) :
    CapturedLowLimbShared132.completed base initial next asset value epoch position column=base column := by
  exact (CapturedHighZeroShared127.early_frame _ initial next asset value epoch position column (by omega) (by omega)).trans
    ((CapturedRegistryHighLimb121.outside _ (asset/2^128) (value/2^128) column (Or.inr (by omega))).trans
      ((FieldZeroSeed125.outside _ 1110 (CapturedHighZeroShared127.difference asset value) column (Or.inr (by omega))).trans
        (CapturedRegistryLowLimb130.outside base (LowBitMeaning128.low asset) (LowBitMeaning128.low value) column (Or.inr lower))))
'''+t[b:]
import re
a=t.index('theorem inside');b=t.index('theorem asset_bits',a);mp={981:1242,982:1243,983:1244,1110:1371};mid=re.sub(r'\b(?:'+'|'.join(map(str,mp))+r')\b',lambda m:str(mp[int(m[0])]),t[a:b]);t=t[:a]+mid+t[b:]
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
theorem next_high (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) (bound : next<2^255) :
    fieldBinary (CapturedNextHighLimb133.leftColumns.map (completed base initial next asset value epoch position))=
      ((next/2^128:Nat):F) :=
  HighBitMeaning122.high_meaning _ 726 next bound (next_bits base initial next asset value epoch position)
theorem asset_high (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) (bound : asset<2^255) :
    fieldBinary (CapturedNextHighLimb133.rightColumns.map (completed base initial next asset value epoch position))=
      ((asset/2^128:Nat):F) :=
  HighBitMeaning122.high_meaning _ 471 asset bound (asset_bits base initial next asset value epoch position)
theorem zero (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) (one : base 0=1) :
    completed base initial next asset value epoch position 0=1 :=
  CapturedLowLimbGlobal131.zero _ initial next asset value epoch position
    ((CapturedNextHighLimb134.outside base _ _ 0 (Or.inl (by decide))).trans one)
'''+t[b:]
t=t.replace('(left : asset<2^255) (right : value<2^255)','(left : next<2^255) (right : asset<2^255)').replace('(178893+index)) 130','(179157+index)) 130').replace('(HighBitMeaning122.high_bound asset left) (HighBitMeaning122.high_bound value right)','(HighBitMeaning122.high_bound next left) (HighBitMeaning122.high_bound asset right)').replace('(asset_high base initial next asset value epoch position left)','(next_high base initial next asset value epoch position left)').replace('(value_high base initial next asset value epoch position right)','(asset_high base initial next asset value epoch position right)')
emit('mac-next-high-global135-source01','CapturedNextHighGlobal135',t,['completed','high_frame','inside','seeded_fixed','final_seeded','next_bits','asset_bits','next_high','asset_high','zero','arithmetic','high_assertions'])
t=(W/'mac-low-limb-shared132-source01/template.lean').read_text().replace('import ShielddSecurity.CapturedLowLimbGlobal131','import ShielddSecurity.CapturedNextHighGlobal135').replace('namespace ShielddSecurity.CapturedLowLimbShared132','namespace ShielddSecurity.CapturedNextHighShared136').replace('end ShielddSecurity.CapturedLowLimbShared132','end ShielddSecurity.CapturedNextHighShared136').replace('abbrev completed := CapturedLowLimbGlobal131.completed','abbrev completed := CapturedNextHighGlobal135.completed')
t=t.replace('CapturedRegistryLowLimb130.seeded base (LowBitMeaning128.low asset) (LowBitMeaning128.low value)','CapturedNextHighLimb134.seeded base (next/2^128) (asset/2^128)').replace('theorem claimed_seed (base : Nat → F) (asset value : Nat)','theorem claimed_seed (base : Nat → F) (next asset : Nat)').replace('CapturedRegistryLowLimb130.outside','CapturedNextHighLimb134.outside')
a=t.index('theorem legal_registry_global1202');b=t.index(' := by',a);stmt=t[a:b].replace('legal_registry_global1202','legal_registry_global1332');c=stmt.index(' :\n    ');stmt=stmt[:c]+stmt[c:].replace(' :\n    ',' :\n    (',1)+''') ∧
    SatisfiesAt (completed base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (179157+index)) 130''';tail=t[b:]
tail=tail.replace('column<1112','column<1242').replace('CapturedRegistryLowLimb130.seeded base (LowBitMeaning128.low w.asset) (LowBitMeaning128.low w.registry.value)','CapturedNextHighLimb134.seeded base (w.registry.nextValue/2^128) (w.asset/2^128)').replace('CapturedHighZeroShared127.legal_registry_global1071','CapturedLowLimbShared132.legal_registry_global1202').replace('(claimed_seed base w.asset w.registry.value group)','(claimed_seed base w.registry.nextValue w.asset group)')
tail=tail.replace('CapturedLowLimbGlobal131.low_assertions','CapturedNextHighGlobal135.high_assertions').replace('w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position⟩','''w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position
    (Nat.lt_trans legal.2.2.2.2.2.2.2.2 CapturedRegistryValueFrame98.modulus_bound)
    (Nat.lt_trans legal.2.2.2.2.2.2.2.1 CapturedRegistryValueFrame98.modulus_bound)⟩''')
emit('mac-next-high-shared136-source01','CapturedNextHighShared136',t[:a]+stmt+tail,['completed','claimed_seed','legal_registry_global1332'])
