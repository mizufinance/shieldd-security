from pathlib import Path
import json,hashlib,argparse
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();assert not a.output.exists();dest=a.output/'source-root/ShielddSecurity';dest.mkdir(parents=True)
data=json.loads((root/'extraction.json').read_text());entries=data['entries'];assert len(entries)==49 and len({e['sourceNode'] for e in entries})==49

def lin(xs):return '['+','.join('('+str(c)+','+str(k)+')' for c,k in sorted(xs))+']'
def row(r):return '⟨'+lin(r['a'])+','+lin(r['b'])+'⟩'
def entry(e):return '⟨'+str(e['sourceNode'])+','+str(e['square']).lower()+','+','.join(lin(e[n]) for n in ['left','right','output','auxiliary'])+','+str(e['start'])+',['+','.join(row(r) for r in e['rows'])+']⟩'
def audit(ns,name):return f'\nset_option pp.all true in\n#check @ShielddSecurity.{ns}.{name}\n#print axioms ShielddSecurity.{ns}.{name}\n'
prefix='-- GENERATED from extraction.json. Do not hand edit.\n';opts='set_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnoncomputable section\n';blocks=[]
for b in range(7):
 ns=f'MapArithmeticCapture705B{b:02d}';blocks.append(ns);s=prefix+'import ShielddSecurity.MapArithmeticAdapter704\n'+opts+f'namespace ShielddSecurity.{ns}\nopen MapArithmeticAdapter704\n'
 for j,e in enumerate(entries[b*7:b*7+7]):s+=f'noncomputable def entry{j} : Entry := '+entry(e)+f'\ntheorem checked{j} : check entry{j}=true := by decide +kernel\n'
 s+='noncomputable def entries : List Entry := ['+','.join(f'entry{j}' for j in range(7))+']\ntheorem checked : entries.all check=true := by\n  simp only [entries,List.all_cons,List.all_nil,'+','.join(f'checked{j}' for j in range(7))+',Bool.true_and]\n'
 s+=f'end ShielddSecurity.{ns}\n'+audit(ns,'checked');(dest/(ns+'.lean')).write_text(s)
ns='MapArithmeticCapture705';s=prefix+''.join('import ShielddSecurity.'+b+'\n' for b in blocks)+opts+f'namespace ShielddSecurity.{ns}\nopen MapArithmeticAdapter704 Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51\n'
s+='noncomputable def entries : List Entry := '+'++'.join(b+'.entries' for b in blocks)+'\ntheorem checked : entries.all check=true := by\n  simp only [entries,List.all_append,'+','.join(b+'.checked' for b in blocks)+',Bool.true_and]\n'
s+='theorem equations {F : Type} [Field F] [CharP F p] (rho : Nat → F)\n    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :\n    ∀ e∈entries, eval rho e.output=if e.square then eval rho e.left*eval rho e.left else eval rho e.left*eval rho e.right := by\n  intro e member\n  exact equation e (List.all_eq_true.mp checked e member) rho arithmetic\n'
s+=f'end ShielddSecurity.{ns}\n'+audit(ns,'checked')+audit(ns,'equations');(dest/(ns+'.lean')).write_text(s)
manifest=dict(runtime_sha=data['runtime_sha'],inputs={n:hashlib.sha256((root/n).read_bytes()).hexdigest() for n in ['generate.py','extraction.json']},modules={p.stem:dict(bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in dest.glob('*.lean')});(a.output/'generation.json').write_text(json.dumps(manifest,indent=2)+'\n')
