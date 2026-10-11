from pathlib import Path
import ast,sys,json,hashlib
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');O=W/'mac-threecall-global-binding173-source11';S=W/'mac-threecall-global-binding173-source12'
def req(v,m):
 if not v:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
req(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags')
req(not S.exists(),'fresh immutable successor');S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());names=[]
for i in range(33,105):
 n='CapturedThreeCallGlobalBinding173J'+f'{i:03d}';names.append(n);count=4 if i==104 else 8
 t=(O/(n+'.template.lean')).read_text();old='theorem count : rows.length='+str(count)+' := by decide +kernel'
 req(t.count(old)==1,'exact count body');t='import ShielddSecurity.TransferPoseidonThreeCallJoin15Proof01\n'+t
 t=t.replace(old,'''theorem count : rows.length='''+str(count)+''' := by
  have total := TransferPoseidonThreeCallJoin15Proof01.row_count
  change (TransferPoseidonThreeCallJoin15Program01.arithmeticRows++[TransferPoseidonWidth3Call08Shared01.rawCopy]).length=1573 at total
  simp only [List.length_append,List.length_singleton] at total
  have size : TransferPoseidonThreeCallJoin15Program01.arithmeticRows.length=1572 := by omega
  change ((TransferPoseidonThreeCallJoin15Program01.arithmeticRows.drop '''+str(736+8*i)+''').take '''+str(count)+''').length='''+str(count)+'''
  rw [List.length_take,List.length_drop,size]
  rfl''')
 (S/(n+'.template.lean')).write_text(t)
n='CapturedThreeCallGlobalBinding173';names.append(n);(S/(n+'.template.lean')).write_bytes((O/(n+'.template.lean')).read_bytes())
g=(O/'generate.py').read_text();a=g.index('for name in [');b=g.index(':\n t=',a);g=g[:a]+'for name in '+repr(names)+g[b:];ast.parse(g);(S/'generate.py').write_text(g)
with(S/'predecessor-provenance01.json').open('x')as f:f.write(json.dumps(dict(predecessor=pin(O/'producer-manifest01.json'),qualified_count_source=pin(W/'mac-poseidon-threecall-join15-source02/source-root/ShielddSecurity/TransferPoseidonThreeCallJoin15Proof01.lean'),scope='Only future J033..104 count proofs/imports change, exact row checker statements/bodies unchanged. Prior33accepted leaves retained; no replay. Root template byteidentical. SOURCE only; all emitted audits UNRUN.'),sort_keys=True,separators=(',',':'))+'\n')
print('72 future symbolic-count leaves+byte-identical root')
