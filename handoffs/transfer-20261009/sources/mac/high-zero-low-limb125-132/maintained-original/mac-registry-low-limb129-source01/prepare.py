from pathlib import Path
import json,re,hashlib
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work')
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
dp=W/'mac-registry-low-limb129-data01/selected-data01.json';d=json.loads(dp.read_bytes());require(pin(dp)['sha256']=='6bb30f2c82b92484125c9548b74957ad2e01ba50bc82aca848d109dbc88a1af1','frozen independent DATA');require(len(d['rows'])==131 and d['borrow']==1112 and d['difference']==1113 and d['bits']==[1114,1242],'actual scope')
S=W/'mac-registry-low-limb129-source01';require(not S.exists(),'fresh');S.mkdir()
t=(W/'mac-registry-high-limb120-source03/template.lean').read_text();t=t.replace('import ShielddSecurity.CapturedAssertions50B0003\n','').replace('CapturedRegistryHighLimb120','CapturedRegistryLowLimb129')
a=t.index('noncomputable def actual');b=t.index('noncomputable def productionCheck');t=t[:a]+'''noncomputable def actual (index : Nat) : Option Row :=
  CapturedAssertions50B0004.block.actual (48+index)
'''+t[b:]
a=t.index('theorem full_position');t=t[:a]+'''theorem full_position (index : Nat) (bound : index<131) :
    CapturedFullRelation58.rowAt (179026+index)=block.actual index := by
  have sum : 179026+index=177954+(1072+index) := by omega
  rw [sum,CapturedFullRelation58.assertion_position (1072+index) (by omega)]
  change (if 1072+index<12288 then _ else _) = _
  rw [if_pos (show 1072+index<12288 by omega)]
  change (if 1072+index<4096 then _ else _) = _
  rw [if_pos (show 1072+index<4096 by omega)]
  change (if 1072+index<2048 then _ else _) = _
  rw [if_pos (show 1072+index<2048 by omega)]
  change (if 1072+index<1024 then _ else _) = _
  rw [if_neg (show ¬1072+index<1024 by omega)]
  change (if 1072+index-1024<512 then _ else _) = _
  rw [if_pos (show 1072+index-1024<512 by omega)]
  change (if 1072+index-1024<256 then _ else _) = _
  rw [if_pos (show 1072+index-1024<256 by omega)]
  have same : 1072+index-1024=48+index := by omega
  change CapturedAssertions50B0004.block.actual (1072+index-1024)=CapturedAssertions50B0004.block.actual (48+index)
  rw [same]
end ShielddSecurity.CapturedRegistryLowLimb129
'''
mp={983:1114,127:128,599:471,344:216,128:129,981:1112,982:1113,130:131}
t=re.sub(r'\b(?:'+ '|'.join(map(str,mp))+r')\b',lambda m:str(mp[int(m[0])]),t[:t.index('theorem full_position')])+t[t.index('theorem full_position'):]
(S/'template.lean').write_text(t);g=(W/'mac-registry-high-limb120-source03/generate.py').read_text().replace('CapturedRegistryHighLimb120','CapturedRegistryLowLimb129');g=g.replace("generator=pin(Path(__file__))","selected_data="+repr(pin(dp))+",generator=pin(Path(__file__))");(S/'generate.py').write_text(g);(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
S=W/'mac-registry-low-limb130-source01';require(not S.exists(),'fresh');S.mkdir();t=(W/'mac-registry-high-limb121-source03/template.lean').read_text().replace('CapturedRegistryHighLimb120','CapturedRegistryLowLimb129').replace('CapturedRegistryHighLimb121','CapturedRegistryLowLimb130');mp={981:1112,982:1113,983:1114,1110:1242,127:128,128:129,130:131,178893:179026};t=re.sub(r'\b(?:'+ '|'.join(map(str,mp))+r')\b',lambda m:str(mp[int(m[0])]),t);(S/'template.lean').write_text(t);g=(W/'mac-registry-high-limb121-source03/generate.py').read_text().replace('CapturedRegistryHighLimb121','CapturedRegistryLowLimb130');(S/'generate.py').write_text(g);(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
print('two maintained low-limb sources prepared')
