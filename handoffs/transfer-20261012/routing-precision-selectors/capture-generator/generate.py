from pathlib import Path
import json,argparse,hashlib,re,os
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();assert not a.output.exists();pending=a.output.with_name(a.output.name+'.pending');assert not pending.exists();dst=pending/'source-root/ShielddSecurity';dst.mkdir(parents=True)
data=json.loads((root/'data.json').read_text());entries=data['entries'];assert [e['index'] for e in entries]==list(range(32))
lc=lambda terms:'['+','.join('('+str(c)+','+str(v)+')' for c,v in terms)+']'
row=lambda r:'⟨'+lc(r[0])+','+lc(r[1])+'⟩'
def product(d):return '⟨'+str(d['source_node'])+',false,'+','.join(lc(d[k]) for k in ['left','right','output','auxiliary'])+','+str(d['start'])+',['+','.join(row(r) for r in d['rows'])+']⟩'
def entry(e):return '⟨'+str(e['index'])+','+product(e['order'])+','+product(e['active'])+','+row(e['orderRow'])+','+row(e['activeRow'])+'⟩'
outputs={}
def header(name,imports):return imports+f'''set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.{name}
open RoutingSelectorAdapter822 Compiler CompilerAssertionBlock51 ConcreteJubjubField01
open RoutingSelectorAlgebra821 (suffix flags)
'''
def emit(name,s,names):
 s+='end ShielddSecurity.'+name+'\n'
 for n in names:s+=f'\nset_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n'
 p=dst/(name+'.lean');p.write_text('-- GENERATED from maintained exact capture; do not edit.\n'+s);outputs[name]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),audits=re.findall(r'^#check @([A-Za-z0-9_.]+)',s,re.M))
chunks=[]
for offset in range(0,32,4):
 name='RoutingSelectorCapture823B'+str(offset//4).zfill(2);chunks.append(name)
 s=header(name,'import ShielddSecurity.RoutingSelectorAdapter822\n')
 s+='noncomputable def entries : List Entry := ['+',\n'.join(entry(e) for e in entries[offset:offset+4])+']\n'
 s+='theorem checked : entries.all check=true := by decide +kernel\n';emit(name,s,['checked'])
sums=[]
for i,d in enumerate(data['sums']):
 name='RoutingSelectorCapture823Sum'+str(i);sums.append(name);pos=d['position'];start=d['start']
 s=header(name,'import ShielddSecurity.RoutingSelectorAdapter822\n')
 s+='noncomputable def row : Row := '+row(d['row'])+'\n'
 s+=f'''theorem captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+{pos}) 1 [row]=true := by decide +kernel
theorem shape : canonical CompilerArithmeticTransport41.p row.a=canonical CompilerArithmeticTransport41.p
    (subtract [(CompilerArithmeticTransport41.copy,1)] (flags {start} (List.range 33))) ∧
    canonical CompilerArithmeticTransport41.p row.b=canonical CompilerArithmeticTransport41.p [] := by decide +kernel

theorem satisfies (rho : Nat → F) (one : rho CompilerArithmeticTransport41.copy=1)
    (sum : eval rho (flags {start} (List.range 33))=1) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+{pos}+i)) 1 :=
  RoutingSelectorAdapter822.sum_row {pos} {start} row captured shape.1 shape.2 rho one sum
''';emit(name,s,['captured','shape','satisfies'])
name='RoutingSelectorCapture823';s=header(name,''.join('import ShielddSecurity.'+n+'\n' for n in chunks+sums))
s+='noncomputable def entries : List Entry := '+'++'.join(n+'.entries' for n in chunks)+'\n'
s+='theorem checked : entries.all check=true := by\n  simp only [entries,List.all_append,'+','.join(n+'.checked' for n in chunks)+',Bool.and_true]\n'
s+='''theorem count : entries.length=32 := by decide +kernel
theorem indices : entries.map Entry.index=List.range 32 := by decide +kernel
noncomputable def entry (index : Fin 32) : Entry := entries[index.val]'(by rw [count];exact index.isLt)
theorem entry_checked (index : Fin 32) : check (entry index)=true :=
  List.all_eq_true.mp checked _ (List.getElem_mem _)
theorem entry_index (index : Fin 32) : (entry index).index=index.val := by
  have slots := congrArg (fun xs : List Nat => xs[index.val]?) indices
  simpa only [List.getElem?_map,List.getElem?_eq_getElem (show index.val<entries.length by rw [count];exact index.isLt),
    List.getElem?_range index.isLt,Option.map_some,Option.some.injEq,entry] using slots

theorem equations (rho : Nat → F) (one : rho CompilerArithmeticTransport41.copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) (index : Fin 32) :
    rho (orderOutput index.val)=eval rho (suffix 19457 index.val)*(1-eval rho (suffix 19523 index.val)) ∧
    rho (activeOutput index.val)=rho 10*(eval rho (suffix 19457 index.val)-eval rho (suffix 19523 index.val)) := by
  have result := RoutingSelectorAdapter822.equations (entry index) (entry_checked index) rho one arithmetic
  simpa only [entry_index] using result

theorem rows (rho : Nat → F) (index : Fin 32) (order : rho (orderOutput index.val)=0)
    (active : let value := eval rho (suffix 19523 index.val)+rho (activeOutput index.val);value*value=value) :
    RoutingSelectorAdapter822.Rows rho index.val := by
  have result := RoutingSelectorAdapter822.rows (entry index) (entry_checked index) rho
    (by simpa only [entry_index] using order) (by simpa only [entry_index] using active)
  simpa only [entry_index] using result
'''
emit(name,s,['checked','count','indices','entry_checked','entry_index','equations','rows'])
(pending/'generation.json').write_text(json.dumps(outputs,indent=2)+'\n');os.replace(pending,a.output)
