"""Maintain bounded block-frame checks and symbolic append; no flat tail walk."""
from pathlib import Path
import re,sys,hashlib,json
if not(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize):raise ValueError('isolated flags')
S=Path(__file__).resolve().parent
P=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/mac-registry-tail-diagnostic06/source-root/ShielddSecurity/CapturedRegistryTail22.lean')
b=P.read_bytes()
if hashlib.sha256(b).hexdigest()!='bad8c45a8f65a6516f1f3cea2164928e54dd4e1c16d5eecb677cd49de4ff8ac4':raise ValueError('handwritten source pin')
# Remove only the maintained early audit lines, then add them at every new declaration.
s=re.sub(r'\nset_option pp.all true in\n#check @[^\n]+\n#print axioms [^\n]+\n','\n',b.decode())
s=s.replace('  fin_cases i <;> decide +kernel','  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by have h:=i.isLt;simp only [Fin.ext_iff];omega\n  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel')
blocks=[('TransferPoseidonCall04R'+str(i).zfill(2)+'.materializedSteps','TransferPoseidonCall04R'+str(i).zfill(2)+'.arithmeticRows.toList') for i in range(2,8)]+[('TransferPoseidonCall04Block'+str(i).zfill(2)+'.steps','TransferPoseidonCall04Block'+str(i).zfill(2)+'.rows') for i in range(1,9)]
t='theorem write_append (a b : List Step) : writeCheck 25088 25460 (a++b)=(writeCheck 25088 25460 a && writeCheck 25088 25460 b) := by\n  simp only [writeCheck,PoseidonCompletion.writes,List.flatMap_append,List.all_append]\n'
t+='theorem support_append (a b : List Row) : supportCheck 25460 (a++b)=(supportCheck 25460 a && supportCheck 25460 b) := by\n  simp only [supportCheck,List.all_append]\n'
for i,(ss,rr) in enumerate(blocks):
 t+=f'theorem block{i} : writeCheck 25088 25460 (CompilerColumnRenaming05.steps ren {ss})=true ∧ supportCheck 25460 (CompilerColumnRenaming05.rows ren {rr})=true := by decide +kernel\n'
t+='theorem copy_bounds : writeCheck 25088 25460 (CompilerColumnRenaming05.steps ren [TransferPoseidonCall04Shared01.copyStep])=true ∧ supportCheck 25460 (CompilerColumnRenaming05.rows ren [TransferPoseidonCall04Shared01.rawCopy])=true := by decide +kernel\n'
base='TransferPoseidonTailTemplate05Program01.'
stepdefs=','.join(base+'prefixSteps'+str(i) for i in range(14));rowdefs=','.join(base+'prefixRows'+str(i) for i in range(14))
t+='theorem bounds : writeCheck 25088 25460 steps=true ∧ supportCheck 25460 rows=true := by\n  constructor\n'
t+='  · simp only [steps,'+base+'steps,'+base+'materializedSteps,'+stepdefs+',CompilerColumnRenaming05.steps,List.map_append,write_append]\n    simp only ['+','.join('block'+str(i)+'.1' for i in range(14))+',copy_bounds.1,Bool.and_self]\n'
t+='  · simp only [rows,'+base+'originalRows,'+base+'arithmeticRows,'+rowdefs+',CompilerColumnRenaming05.rows,List.map_append,support_append]\n    simp only ['+','.join('block'+str(i)+'.2' for i in range(14))+',copy_bounds.2,Bool.and_self]\n'
old='theorem bounds : writeCheck 25088 25460 steps=true ∧ supportCheck 25460 rows=true := by decide +kernel'
if s.count(old)!=1:raise ValueError('unique bounds replacement')
s=s.replace(old,t.rstrip())
a=s.index('theorem counts :');z=s.index('\nvariable',a)
s=s[:a]+'''theorem counts : steps.length=280 ∧ rows.length=373 ∧ TransferPoseidonTailTemplate05Program01.materializedSteps.length=279 ∧ TransferPoseidonTailTemplate05Program01.arithmeticRows.length=372 := by
  have stepCount : steps.length=280 := by
    simpa only [steps,CompilerColumnRenaming05.steps,List.length_map] using TransferPoseidonTailTemplate05Program01.step_count
  have rowCount : rows.length=373 := by
    simpa only [rows,CompilerColumnRenaming05.rows,List.length_map] using TransferPoseidonTailTemplate05Program01.row_count
  have arithmeticCount : TransferPoseidonTailTemplate05Program01.arithmeticRows.length=372 := by
    have h:=TransferPoseidonTailTemplate05Program01.row_count
    simp only [TransferPoseidonTailTemplate05Program01.originalRows,List.length_append,List.length_singleton] at h
    omega
  exact ⟨stepCount,rowCount,TransferPoseidonTailTemplate05Program01.materialized_count,arithmeticCount⟩
'''+s[z:]
a=s.index('theorem bounds :');z=s.index('theorem counts :',a)
section=s[a:z]
locals=''.join('  have b'+str(i)+' := block'+str(i)+'\n  simp only [CompilerColumnRenaming05.steps,CompilerColumnRenaming05.rows] at b'+str(i)+'\n' for i in range(14))
locals+='  have bc := copy_bounds\n  simp only [CompilerColumnRenaming05.steps,CompilerColumnRenaming05.rows] at bc\n'
section=section.replace('  constructor\n',locals+'  constructor\n')
for i in range(14):section=section.replace('block'+str(i)+'.','b'+str(i)+'.')
section=section.replace('copy_bounds.','bc.')
s=s[:a]+section+s[z:]
parts=re.split(r'(?=^(?:def|theorem|variable|end)\b)',s,flags=re.M);out=''
for part in parts:
 out+=part;m=re.match(r'(?:def|theorem) (\w+)',part)
 if m:
  n='ShielddSecurity.R22.'+m.group(1);out+='\nset_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n'
bb=out.encode();p=S/'source-root/ShielddSecurity/CapturedRegistryTail22.lean';p.parent.mkdir(parents=True,exist_ok=True)
if p.exists():
 if p.read_bytes()!=bb:raise ValueError('immutable mismatch')
else:
 with p.open('xb')as f:f.write(bb)
print(json.dumps(dict(bytes=len(bb),sha256=hashlib.sha256(bb).hexdigest())))
