from pathlib import Path
import argparse,json,hashlib
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();assert not a.output.exists();dest=a.output/'source-root/ShielddSecurity';dest.mkdir(parents=True)
families=json.loads((root/'families.json').read_text());assert len(families)==3
def lin(xs):return '['+','.join('('+str(c)+','+str(k)+')' for c,k in xs)+']'
def audit(ns,n):return f'\nset_option pp.all true in\n#check @ShielddSecurity.{ns}.{n}\n#print axioms ShielddSecurity.{ns}.{n}\n'
opts='set_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnoncomputable section\n'
for f in families:
 ns=f'MapCofactorCapture713F{f["phase"]:02d}';imports=sorted({f'MapArithmeticCapture705B{i//7:02d}' for i in f['indices']});s='-- GENERATED from families.json. Do not hand edit.\nimport ShielddSecurity.MapCofactorAdapter712\nimport Mathlib.Tactic.IntervalCases\n'+''.join('import ShielddSecurity.'+n+'\n' for n in imports)+opts+f'namespace ShielddSecurity.{ns}\nopen MapCofactorAdapter712 CompilerAssertionBlock51 ConcreteJubjubField01\n'
 s+='noncomputable def layout : Layout := ⟨'+lin(f['x'])+','+lin(f['y'])+','+str(f['hint'])+','+str(f['start'])+'⟩\n'
 for j,i in enumerate(f['indices']):s+=f'theorem checked{j} : check layout {j} MapArithmeticCapture705B{i//7:02d}.entry{i%7}=true := by decide +kernel\n'
 s+='theorem equations (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :\n    ∀ index<11, Equation rho layout index := by\n  intro index bound\n  interval_cases index\n'
 for j,i in enumerate(f['indices']):s+=f'  · exact equation layout {j} MapArithmeticCapture705B{i//7:02d}.entry{i%7} checked{j} MapArithmeticCapture705B{i//7:02d}.checked{i%7} rho arithmetic\n'
 s+=f'end ShielddSecurity.{ns}\n'+audit(ns,'equations');(dest/(ns+'.lean')).write_text(s)
ns='MapCofactorCapture713';s='-- GENERATED from families.json. Do not hand edit.\n'+''.join(f'import ShielddSecurity.MapCofactorCapture713F{f["phase"]:02d}\n' for f in families)+opts+f'namespace ShielddSecurity.{ns}\nopen MapCofactorAdapter712 CompilerAssertionBlock51 ConcreteJubjubField01\n'
s+='theorem equations (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :\n'+ ' ∧\n'.join(f'    (∀ index<11, Equation rho MapCofactorCapture713F{f["phase"]:02d}.layout index)' for f in families)+' :=\n  ⟨'+','.join(f'MapCofactorCapture713F{f["phase"]:02d}.equations rho arithmetic' for f in families)+'⟩\n'
s+=f'end ShielddSecurity.{ns}\n'+audit(ns,'equations');(dest/(ns+'.lean')).write_text(s)
(a.output/'generation.json').write_text(json.dumps(dict(runtime_sha='844389ee069e1fb2e576708842d0b389b4d9a44a',inputs={n:hashlib.sha256((root/n).read_bytes()).hexdigest() for n in ['families.json','generate.py']},modules={p.stem:dict(bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in dest.glob('*.lean')}),indent=2)+'\n')
