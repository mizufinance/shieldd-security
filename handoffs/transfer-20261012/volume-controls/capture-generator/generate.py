from pathlib import Path
import json,argparse,os,re,hashlib
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();assert not a.output.exists();pending=a.output.with_name(a.output.name+'.pending');assert not pending.exists();dst=pending/'source-root/ShielddSecurity';dst.mkdir(parents=True)
data=json.loads((root/'data.json').read_text());assert [e['positions'] for e in data['entries']]==[[7462,7463],[7465,7466],[7468,7469],[7471,7472]]
lc=lambda terms:'['+','.join('('+str(c)+','+str(v)+')' for c,v in terms)+']'
row=lambda r:'⟨'+lc(r[0])+','+lc(r[1])+'⟩'
outputs={}
def emit(name,s,names):
 s+='end ShielddSecurity.'+name+'\n'
 for n in names:s+=f'\nset_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n'
 p=dst/(name+'.lean');p.write_text('-- GENERATED from maintained exact capture; do not edit.\n'+s);outputs[name]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),audits=re.findall(r'^#check @([A-Za-z0-9_.]+)',s,re.M))
def header(name,imports='import ShielddSecurity.MapArithmeticAdapter704\n'):
 return imports+f'''set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.{name}
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 MapArithmeticAdapter704
'''
for e in data['entries']:
 name='VolumeControlCapture804F'+str(e['slot']);s=header(name);names=[]
 for prefix,d in zip(['inverse','zero'],e['products']):
  pos=d['position'];out=d['output'][0][0];hint=d['right'][0][0];left,right=[x[0] for x in d['left']];flag=e['flag']
  s+='noncomputable def '+prefix+'Entry : Entry := ⟨'+str(d['source_node'])+',false,'+','.join(lc(d[k]) for k in ['left','right','output','auxiliary'])+','+str(d['start'])+',['+','.join(row(r) for r in d['rows'])+']⟩\n'
  s+='noncomputable def '+prefix+'Rows : List Row := ['+row(d['assertion'])+']\n'
  s+=f'''theorem {prefix}_checked : check {prefix}Entry=true := by decide +kernel

theorem {prefix}_equation (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho {out}=(rho {left}-rho {right})*rho {hint} := by
  have result := MapArithmeticAdapter704.equation {prefix}Entry {prefix}_checked rho arithmetic
  have shape : canonical p {lc(d['left'])}=canonical p [({left},1),({right},-1)] := by decide +kernel
  simp only [{prefix}Entry,Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ shape] at result
  simpa only [eval,Int.cast_one,one_mul,Int.cast_neg,add_zero,neg_mul,sub_eq_add_neg] using result

theorem {prefix}_captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+{pos}) 1 {prefix}Rows=true := by decide +kernel
'''
  names += [prefix+'_checked',prefix+'_equation',prefix+'_captured']
 inv=e['products'][0]['output'][0][0];zero=e['products'][1]['output'][0][0];p0,p1=e['positions'];flag=e['flag']
 s+=f'''theorem rows (rho : Nat → F) (one : rho copy=1)
    (inverse : rho {inv}=1-rho {flag}) (zero : rho {zero}=0) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+{p0}+i)) 1 ∧
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+{p1}+i)) 1 := by
  constructor
  · apply (CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt (177954+{p0}) 1 inverseRows inverse_captured rho).mp
    intro row member
    simp only [inverseRows,List.mem_cons,List.not_mem_nil,or_false] at member
    subst row
    change eval rho [({flag},1),({inv},1),(copy,(p:Int)-1)]*eval rho [({flag},1),({inv},1),(copy,(p:Int)-1)]=eval rho []
    have shape : canonical p [({flag},1),({inv},1),(copy,(p:Int)-1)]=canonical p [({flag},1),({inv},1),(copy,-1)] := by decide +kernel
    rw [canonical_equal rho _ _ shape]
    simp only [eval,Int.cast_one,one_mul,Int.cast_neg,add_zero,one,inverse]
    ring
  · apply (CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt (177954+{p1}) 1 zeroRows zero_captured rho).mp
    intro row member
    simp only [zeroRows,List.mem_cons,List.not_mem_nil,or_false] at member
    subst row
    change eval rho [({zero},(p:Int)-1)]*eval rho [({zero},(p:Int)-1)]=eval rho []
    simp only [eval,add_zero,zero,mul_zero]
'''
 names+=['rows'];emit(name,s,names)
name='VolumeControlCapture804Context';s=header(name);s+='noncomputable def rows : List Row := ['+row(data['context'])+']\n';s+='''theorem checked : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+7475) 1 rows=true := by decide +kernel

theorem satisfies (rho : Nat → F) (one : rho copy=1)
    (boolean : (rho 7607-1)*(rho 7607-1)=rho 7607-1) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+7475+i)) 1 := by
  apply (CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt (177954+7475) 1 rows checked rho).mp
  intro row member
  simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at member
  subst row
  change eval rho [(7607,1),(copy,(p:Int)-1)]*eval rho [(7607,1),(copy,(p:Int)-1)]=eval rho [(7607,1),(copy,(p:Int)-1)]
  have shape : canonical p [(7607,1),(copy,(p:Int)-1)]=canonical p [(7607,1),(copy,-1)] := by decide +kernel
  rw [canonical_equal rho _ _ shape]
  simpa only [eval,Int.cast_one,one_mul,Int.cast_neg,add_zero,one,neg_mul,mul_one,sub_eq_add_neg] using boolean
''';emit(name,s,['checked','satisfies'])
name='VolumeControlCapture804';imports=''.join('import ShielddSecurity.VolumeControlCapture804F'+str(i)+'\n' for i in range(4))+'import ShielddSecurity.VolumeControlCapture804Context\nimport ShielddSecurity.VolumeControlBindings803\n';s=header(name,imports)
s+='''def firstPosition (slot : Fin 4) : Nat := 7462+3*slot.val
def inverseOutput (slot : Fin 4) : Nat := if slot.val=0 then 108438 else if slot.val=1 then 108442 else if slot.val=2 then 108448 else 108454
def zeroOutput (slot : Fin 4) : Nat := if slot.val=0 then 108440 else if slot.val=1 then 108444 else if slot.val=2 then 108450 else 108456

def FamilyRows (rho : Nat → F) (slot : Fin 4) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+firstPosition slot+i)) 1 ∧
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+firstPosition slot+1+i)) 1

def Rows (rho : Nat → F) : Prop :=
  (∀ slot : Fin 4,FamilyRows rho slot) ∧ SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+7475+i)) 1

theorem equations (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) (slot : Fin 4) :
    rho (inverseOutput slot)=(rho (VolumeControlBindings803.leftColumn slot)-rho (VolumeControlBindings803.rightColumn slot))*rho (7598+2*slot.val) ∧
    rho (zeroOutput slot)=(rho (VolumeControlBindings803.leftColumn slot)-rho (VolumeControlBindings803.rightColumn slot))*rho (7597+2*slot.val) := by
  rcases slot with ⟨slot,bound⟩
  have cases : slot=0 ∨ slot=1 ∨ slot=2 ∨ slot=3 := by omega
  rcases cases with rfl|rfl|rfl|rfl
'''
for i in range(4):s+=f'  · exact ⟨VolumeControlCapture804F{i}.inverse_equation rho arithmetic,VolumeControlCapture804F{i}.zero_equation rho arithmetic⟩\n'
s+='''
theorem family_rows (rho : Nat → F) (one : rho copy=1) (slot : Fin 4)
    (inverse : rho (inverseOutput slot)=1-rho (7597+2*slot.val)) (zero : rho (zeroOutput slot)=0) : FamilyRows rho slot := by
  rcases slot with ⟨slot,bound⟩
  have cases : slot=0 ∨ slot=1 ∨ slot=2 ∨ slot=3 := by omega
  rcases cases with rfl|rfl|rfl|rfl
'''
for i in range(4):s+=f'  · exact VolumeControlCapture804F{i}.rows rho one inverse zero\n'
s+='''
theorem rows (rho : Nat → F) (one : rho copy=1)
    (families : ∀ slot : Fin 4,FamilyRows rho slot)
    (boolean : (rho 7607-1)*(rho 7607-1)=rho 7607-1) : Rows rho :=
  ⟨families,VolumeControlCapture804Context.satisfies rho one boolean⟩
''';emit(name,s,['FamilyRows','Rows','equations','family_rows','rows'])
(pending/'generation.json').write_text(json.dumps(outputs,indent=2)+'\n');os.replace(pending,a.output)
