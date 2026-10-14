"""Generate exact point-equality checks from the captured publication rows."""
from pathlib import Path
import argparse, hashlib, json, os

root = Path(__file__).resolve().parent
ap = argparse.ArgumentParser()
ap.add_argument('output', type=Path)
a = ap.parse_args()
assert not a.output.exists()
pending = a.output.with_name(a.output.name + '.pending')
dest = pending / 'source-root/ShielddSecurity'
dest.mkdir(parents=True)
inventory = {}

def lc(terms):
    return '[' + ','.join(f'({c},{v})' for c,v in terms) + ']'

def emit(name, imports, body, audits):
    source = '-- GENERATED from entries.json by generate.py. Do not hand edit.\n'
    source += ''.join('import ShielddSecurity.'+n+'\n' for n in imports)
    source += 'set_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnoncomputable section\n'
    source += 'namespace ShielddSecurity.'+name+'\nopen Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51\n'
    source += body+'\nend ShielddSecurity.'+name+'\n'
    names = ['ShielddSecurity.'+name+'.'+n for n in audits]
    for n in names:
        source += '\nset_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n'
    p = dest/(name+'.lean')
    p.write_text(source)
    inventory[name] = dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(), audits=names)

entries = json.loads((root/'entries.json').read_text())
assert [e['family'] for e in entries] == list(range(8))
leaves = []
for e in entries:
    name = 'FixedPublishedRows580F'+str(e['family']).zfill(2)
    leaves.append(name)
    left,right,start=e['left'],e['right'],e['position']
    rows='['+','.join('⟨'+lc(x)+','+lc(y)+'⟩' for x,y in e['rows'])+']'
    body=f'''def entry : PointEqualityAdapter440.Entry :=
  ⟨[({left},1)],[({left+1},1)],[({right},1)],[({right+1},1)],{start},{rows}⟩
theorem checked : PointEqualityAdapter440.check entry=true := by decide +kernel
theorem rows_iff {{F : Type}} [Field F] [CharP F p] (rho : Nat → F) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+{start}+i)) 2 ↔
    VariableWindowColumns449.columnPoint rho {left}=VariableWindowColumns449.columnPoint rho {right} := by
  have equivalence := PointEqualityAdapter440.equality_iff entry checked rho
  change SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+{start}+i)) 2 ↔
    Group.Point.mk (eval rho [({left},1)]) (eval rho [({left+1},1)])=
    Group.Point.mk (eval rho [({right},1)]) (eval rho [({right+1},1)]) at equivalence
  simpa only [eval,Int.cast_one,one_mul,add_zero,VariableWindowColumns449.columnPoint] using equivalence
'''
    emit(name,['PointEqualityAdapter440','VariableWindowColumns449'],body,['entry','checked','rows_iff'])

def ns(field):
    return '['+','.join(str(e[field]) for e in entries)+'][family.val]!'
body = 'def position (family : Fin 8) : Nat := '+ns('position')+'\n'
body += 'def leftColumn (family : Fin 8) : Nat := '+ns('left')+'\n'
body += 'def rightColumn (family : Fin 8) : Nat := '+ns('right')+'\n'
body += '''theorem rows_iff {F : Type} [Field F] [CharP F p] (rho : Nat → F) (family : Fin 8) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+position family+i)) 2 ↔
    VariableWindowColumns449.columnPoint rho (leftColumn family)=
      VariableWindowColumns449.columnPoint rho (rightColumn family) := by
  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ ∨ family=⟨2,by decide⟩ ∨
      family=⟨3,by decide⟩ ∨ family=⟨4,by decide⟩ ∨ family=⟨5,by decide⟩ ∨
      family=⟨6,by decide⟩ ∨ family=⟨7,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
'''
for name in leaves:
    body += '  · exact '+name+'.rows_iff rho\n'
emit('FixedPublishedRows580',leaves,body,['position','leftColumn','rightColumn','rows_iff'])
(pending/'generation.json').write_text(json.dumps(inventory,indent=2,sort_keys=True)+'\n')
os.replace(pending,a.output)
print(json.dumps(dict(modules=len(inventory),rows=16,proof_credit=0)))
