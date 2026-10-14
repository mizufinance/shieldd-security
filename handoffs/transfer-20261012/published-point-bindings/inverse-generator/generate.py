from pathlib import Path
import argparse,json,re,os,hashlib
root=Path(__file__).resolve().parent;ap=argparse.ArgumentParser();ap.add_argument('output',type=Path);a=ap.parse_args();assert not a.output.exists();pending=a.output.with_name(a.output.name+'.pending');dest=pending/'source-root/ShielddSecurity';dest.mkdir(parents=True);entries=json.loads((root/'entries.json').read_text());template=(root/'leaf.lean.in').read_text();inventory={}
def emit(name,s):
 names=re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)',s,re.M)
 for n in names:s+=f'\nset_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n'
 path=dest/(name+'.lean');path.write_text(s);inventory[name]=dict(sha256=hashlib.sha256(path.read_bytes()).hexdigest(),audits=['ShielddSecurity.'+name+'.'+n for n in names])
def lc(ts):return '['+','.join(f'({c},{v})' for c,v in ts)+']'
leaves=[]
for e in entries:
 name='PublishedInverse588F'+str(e['family']).zfill(2);leaves.append(name)
 literal='['+','.join('⟨'+lc(a)+','+lc(b)+'⟩' for a,b in e['rows'])+']'
 s=template.replace('CapturedRkInverse508',name)
 for old,new in [('41788',e['arithmeticStart']),('4272',e['operand']),('4279',e['hint']),('4287',e['position'])]:s=s.replace(old,str(new))
 s=s.replace('RAW_ROWS',literal).replace('-- GENERATED from rows.json by generate.py. Do not hand edit.','-- GENERATED from entries.json and leaf.lean.in. Do not hand edit.')
 emit(name,s)
s='-- GENERATED from entries.json by generate.py. Do not hand edit.\n'+''.join('import ShielddSecurity.'+n+'\n' for n in leaves)+'''set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PublishedInverse588
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
'''
for field in ['position','operand','hint','output']:s+='def '+field+' (family : Fin 8) : Nat := ['+','.join(str(e[field]) for e in entries)+'][family.val]!\n'
s+='''variable {F : Type} [Field F] [CharP F p]
def Rows (rho : Nat → F) (family : Fin 8) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+(position family+i))) 1
'''
cases='''  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ ∨ family=⟨2,by decide⟩ ∨
      family=⟨3,by decide⟩ ∨ family=⟨4,by decide⟩ ∨ family=⟨5,by decide⟩ ∨
      family=⟨6,by decide⟩ ∨ family=⟨7,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
'''
s+='''theorem products (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (family : Fin 8) : rho (output family)=rho (operand family)*rho (hint family) := by
'''+cases
for n in leaves:s+='  · simpa only ['+n+'.output,'+n+'.arithmeticStart,'+n+'.operandTerms,'+n+'.hintColumn,eval,Int.cast_one,one_mul,add_zero] using '+n+'.products rho arithmetic 0 (by decide)\n'
s+='''theorem complete (rho : Nat → F) (zero : rho 0=1) (linked : rho copy=rho 0)
    (family : Fin 8) (value : rho (output family)=1) : Rows rho family := by
'''+cases
for n in leaves:s+='  · apply '+n+'.complete rho zero linked\n    intro index bound\n    have equal : index=0 := by omega\n    subst index\n    exact value\n'
s+='''theorem sound (rho : Nat → F) (zero : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (family : Fin 8) (rows : Rows rho family) : rho (operand family)≠0 := by
'''+cases
for n in leaves:s+='  · simpa only ['+n+'.operandTerms,eval,Int.cast_one,one_mul,add_zero] using '+n+'.sound rho zero linked arithmetic rows 0 (by decide)\n'
s+='end ShielddSecurity.PublishedInverse588\n';emit('PublishedInverse588',s)
(pending/'generation.json').write_text(json.dumps(inventory,indent=2)+'\n');os.replace(pending,a.output);print(json.dumps(dict(modules=len(inventory),audits=sum(len(v['audits']) for v in inventory.values()))))
