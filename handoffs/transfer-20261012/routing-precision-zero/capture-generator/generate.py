from pathlib import Path
import json,argparse,hashlib,re,os
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();assert not a.output.exists();pending=a.output.with_name(a.output.name+'.pending');assert not pending.exists();dst=pending/'source-root/ShielddSecurity';dst.mkdir(parents=True)
data=json.loads((root/'data.json').read_text());entries=data['entries'];assert [e['slot'] for e in entries]==list(range(66))
lc=lambda terms:'['+','.join('('+str(c)+','+str(v)+')' for c,v in terms)+']'
row=lambda r:'⟨'+lc(r[0])+','+lc(r[1])+'⟩'
def product(d):return '⟨'+str(d['source_node'])+',false,'+','.join(lc(d[k]) for k in ['left','right','output','auxiliary'])+','+str(d['start'])+',['+','.join(row(r) for r in d['rows'])+']⟩'
def entry(e):return '⟨'+str(e['slot'])+','+product(e['inverse'])+','+product(e['zero'])+','+row(e['inverseRow'])+','+row(e['zeroRow'])+'⟩'
outputs={}
def header(name,imports):return imports+f'''set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.{name}
open RoutingPrecisionAdapter817 Compiler CompilerAssertionBlock51 ConcreteJubjubField01
'''
def emit(name,s,names):
 s+='end ShielddSecurity.'+name+'\n'
 for n in names:s+=f'\nset_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n'
 p=dst/(name+'.lean');p.write_text('-- GENERATED from maintained exact capture; do not edit.\n'+s);outputs[name]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),audits=re.findall(r'^#check @([A-Za-z0-9_.]+)',s,re.M))
chunks=[]
for offset in range(0,66,8):
 name='RoutingPrecisionCapture818B'+str(offset//8).zfill(2);chunks.append(name)
 s=header(name,'import ShielddSecurity.RoutingPrecisionAdapter817\n')
 s+='noncomputable def entries : List Entry := ['+',\n'.join(entry(e) for e in entries[offset:offset+8])+']\n'
 s+='theorem checked : entries.all check=true := by decide +kernel\n';emit(name,s,['checked'])
name='RoutingPrecisionCapture818';s=header(name,''.join('import ShielddSecurity.'+n+'\n' for n in chunks))
s+='noncomputable def entries : List Entry := '+'++'.join(n+'.entries' for n in chunks)+'\n'
s+='theorem checked : entries.all check=true := by\n  simp only [entries,List.all_append,'+','.join(n+'.checked' for n in chunks)+',Bool.and_true]\n'
s+='''theorem count : entries.length=66 := by decide +kernel
theorem indices : entries.map Entry.slot=List.range 66 := by decide +kernel
noncomputable def entry (slot : Fin 66) : Entry := entries[slot.val]'(by rw [count];exact slot.isLt)
theorem entry_checked (slot : Fin 66) : check (entry slot)=true :=
  List.all_eq_true.mp checked _ (List.getElem_mem _)
theorem entry_slot (slot : Fin 66) : (entry slot).slot=slot.val := by
  have slots := congrArg (fun xs : List Nat => xs[slot.val]?) indices
  simpa only [List.getElem?_map,List.getElem?_eq_getElem (show slot.val<entries.length by rw [count];exact slot.isLt),
    List.getElem?_range slot.isLt,Option.map_some,Option.some.injEq,entry] using slots

theorem equations (rho : Nat → F) (one : rho CompilerArithmeticTransport41.copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) (slot : Fin 66) :
    rho (inverseOutput slot.val)=(rho (inputColumn slot.val)-((slot.val%33:Nat):F))*rho (hintColumn slot.val) ∧
    rho (zeroOutput slot.val)=(rho (inputColumn slot.val)-((slot.val%33:Nat):F))*rho (flagColumn slot.val) := by
  have result := RoutingPrecisionAdapter817.equations (entry slot) (entry_checked slot) rho one arithmetic
  simpa only [entry_slot] using result

theorem rows (rho : Nat → F) (one : rho CompilerArithmeticTransport41.copy=1) (slot : Fin 66)
    (inverse : rho (inverseOutput slot.val)=1-rho (flagColumn slot.val)) (zero : rho (zeroOutput slot.val)=0) :
    RoutingPrecisionAdapter817.Rows rho slot.val := by
  have result := RoutingPrecisionAdapter817.rows (entry slot) (entry_checked slot) rho one
    (by simpa only [entry_slot] using inverse) (by simpa only [entry_slot] using zero)
  simpa only [entry_slot] using result
'''
emit(name,s,['checked','count','indices','entry_checked','entry_slot','equations','rows'])
(pending/'generation.json').write_text(json.dumps(outputs,indent=2)+'\n');os.replace(pending,a.output)
