from pathlib import Path
import json,sys,hashlib
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');O=W/'mac-registry-global-binding175-source02';S=W/'mac-registry-global-binding175-source03'
def require(v,m):
 if not v:raise ValueError(m)
require(sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site and not sys.flags.optimize,'isolated')
require(not S.exists(),'fresh source successor')
names=[];modules={}
for i,offset in enumerate(range(0,416,16)):
 n='CapturedRegistryGlobalBinding175G'+f'{i:02d}';names.append(n)
 body=(O/'CapturedRegistryGlobalBinding175C00.template.lean').read_text().replace('CapturedRegistryGlobalBinding175C00',n).replace('.drop 0','.drop '+str(offset)).replace('.take 64','.take 16').replace("List.range' 2306 64","List.range' "+str(2306+offset)+' 16').replace('rows.length=64','rows.length=16')
 modules[n]=dict(body=body,names=['rows','indices','productionCheck','checked','count','sound'])
t=(O/'CapturedRegistryGlobalBinding175.template.lean').read_text()
for i in range(7):t=t.replace('import ShielddSecurity.CapturedRegistryGlobalBinding175C'+f'{i:02d}'+'\n','')
t=''.join('import ShielddSecurity.'+n+'\n'for n in names)+t.replace('import ShielddSecurity.CompilerSelectedChunks172','import ShielddSecurity.CompilerIndexedSlices183')
t=t.replace('CompilerArithmeticTransport41 CompilerSelectedChunks172','CompilerArithmeticTransport41 CompilerSelectedChunks172 CompilerIndexedSlices183')
t=t.replace('theorem count : arithmeticRows.length=416 := by decide +kernel','theorem count : arithmeticRows.length=416 := by\n  rw [arithmeticRows,List.length_take,RegistryWhole23.row_count.1]\n  rfl')
widths='['+','.join(['16']*26)+']'
t=t.replace('slices arithmeticRows [64,64,64,64,64,64,32]','slicesAt arithmeticRows 0 '+widths)
a=t.index('theorem partition');b=t.index('theorem copy_tail',a)
t=t[:a]+'''theorem partition : chunks.flatten=arithmeticRows := by
  apply CompilerIndexedSlices183.partition
  rw [count]
  decide
'''+t[b:]
a=t.index('theorem copy_tail');b=t.index('theorem selected_partition',a)
t=t[:a]+'''theorem copy_tail : RegistryWhole23.selectedRows.drop 416=[TransferPoseidonCall04Shared01.rawCopy] := by
  change (((RegistryWhole23.D0.arithmeticRows++RegistryWhole23.D1.arithmeticRows)++RegistryWhole23.tailArithmetic)++[TransferPoseidonCall04Shared01.rawCopy]).drop 416=_
  apply List.drop_left'
  have length := RegistryWhole23.row_count.1
  simp only [RegistryWhole23.selectedRows,List.length_append,List.length_singleton] at length ⊢
  omega
'''+t[b:]
a=t.index('  change AllSatisfied rho [');b=t.index('\ntheorem sound',a)
t=t[:a]+'  change AllSatisfied rho ['+','.join(n+'.rows'for n in names)+']\n  exact '+''.join('⟨'+n+'.sound rho satisfied,'for n in names)+'True.intro'+'⟩'*len(names)+'\n'+t[b:]
modules['CapturedRegistryGlobalBinding175']=dict(body=t,names=['arithmeticRows','count','chunks','partition','copy_tail','selected_partition','copyCheck','copy_checked','arithmetic_sound','sound'])
inputs={}
for p in [O/'CapturedRegistryGlobalBinding175.template.lean',O/'CapturedRegistryGlobalBinding175C00.template.lean',W/'mac-indexed-slices183-source01/source-root/ShielddSecurity/CompilerIndexedSlices183.lean']:
 b=p.read_bytes();inputs[str(p)]=dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
S.mkdir();(S/'generate.py').write_bytes((W/'mac-indexed-slices183-source01/generate.py').read_bytes());(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
with(S/'templates01.json').open('x')as f:f.write(json.dumps(dict(modules=modules,inputs=inputs,scope='SOURCE-only sixteen-row bounded successor replacing UNRUN64-row grouping. Exact416arithmetic+ONEcopy; independent actual indexed relation is only row-truth antecedent. All new audits UNRUN; no heap/cap escalation/accepted replay/history change.'),sort_keys=True,separators=(',',':'))+'\n')
print(json.dumps(dict(stage=str(S),modules=len(modules))))
