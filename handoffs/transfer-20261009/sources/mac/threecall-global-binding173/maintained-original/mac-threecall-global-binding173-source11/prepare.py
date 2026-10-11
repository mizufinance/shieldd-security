from pathlib import Path
import ast,sys
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');O=W/'mac-threecall-global-binding173-source09';S=W/'mac-threecall-global-binding173-source11'
def req(v,m):
 if not v:raise ValueError(m)
req(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated')
req(not S.exists(),'fresh immutable source');S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());names=[]
source=(O/'CapturedThreeCallGlobalBinding173H030.template.lean').read_text()
for i,offset in enumerate(range(736,1572,8)):
 n='CapturedThreeCallGlobalBinding173J'+f'{i:03d}';names.append(n);count=min(8,1572-offset)
 t=source.replace('CapturedThreeCallGlobalBinding173H030',n).replace('.drop 736','.drop '+str(offset)).replace('.take 16','.take '+str(count)).replace("List.range' 1470 16","List.range' "+str(734+offset)+' '+str(count)).replace('rows.length=16','rows.length='+str(count))
 (S/(n+'.template.lean')).write_text(t)
t=(O/'CapturedThreeCallGlobalBinding173.template.lean').read_text()
for i in range(30,83):t=t.replace('import ShielddSecurity.CapturedThreeCallGlobalBinding173H'+f'{i:03d}'+'\n','')
a=t.index('import ShielddSecurity.CompilerSelectedChunks172');t=t[:a]+''.join('import ShielddSecurity.'+n+'\n'for n in names)+t[a:]
a=t.index('noncomputable def chunks');b=t.index('\ntheorem partition',a)
t=t[:a]+'noncomputable def chunks : List (List Row) := indexedSlices arithmeticRows 0 '+repr([32]*7+[16]*32+[8]*104+[4]).replace(' ','')+'\n'+t[b:]
allnames=['CapturedJoinPack179Pilot32']+['CapturedThreeCallGlobalBinding173D'+f'{i:03d}'for i in range(6)]+['CapturedThreeCallGlobalBinding173F0','CapturedThreeCallGlobalBinding173F1']+['CapturedThreeCallGlobalBinding173H'+f'{i:03d}'for i in range(30)]+names
req(sum([32]*7+[16]*32+[8]*104+[4])==1572 and len(allnames)==144,'exact full partition reused736/new836')
a=t.index('  change AllSatisfied rho [');b=t.index('\ntheorem sound',a)
t=t[:a]+'  change AllSatisfied rho ['+','.join(n+'.rows'for n in allnames)+']\n  exact '+''.join('⟨'+n+'.sound rho satisfied,'for n in allnames)+'True.intro'+'⟩'*len(allnames)+'\n'+t[b:]
oldwidths=repr([32]*7+[16]*84+[4]).replace(' ','');newwidths=repr([32]*7+[16]*32+[8]*104+[4]).replace(' ','')
req(t.count('have total : '+oldwidths+'.sum=1572')==1,'exact predecessor partition literal')
t=t.replace('have total : '+oldwidths+'.sum=1572','have total : '+newwidths+'.sum=1572')
t='import ShielddSecurity.TransferPoseidonThreeCallJoin15Proof01\n'+t
req(t.count('theorem count : arithmeticRows.length=1572 := by decide +kernel')==1,'exact symbolic count repair')
t=t.replace('theorem count : arithmeticRows.length=1572 := by decide +kernel','''theorem count : arithmeticRows.length=1572 := by
  have total := TransferPoseidonThreeCallJoin15Proof01.row_count
  change (arithmeticRows++[TransferPoseidonWidth3Call08Shared01.rawCopy]).length=1573 at total
  simp only [List.length_append,List.length_singleton] at total
  omega''')
(S/'CapturedThreeCallGlobalBinding173.template.lean').write_text(t)
g=(O/'generate.py').read_text();a=g.index('for name in [');b=g.index(':\n t=',a);g=g[:a]+'for name in '+repr(names+['CapturedThreeCallGlobalBinding173'])+g[b:];ast.parse(g);(S/'generate.py').write_text(g)
print('105 new8-row leaves+one root; all30acceptedH reused')
