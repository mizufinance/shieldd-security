#!/usr/bin/env python3
"""Reproduce the exact 38 checked field-certificate modules in a fresh directory."""
from pathlib import Path
import hashlib,json

import argparse
if not __debug__:
    raise RuntimeError('optimized Python is forbidden: validation uses assertions')
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--candidate', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True, help='fresh package directory; ShielddSecurity and manifest.json are created inside')
args=parser.parse_args()
source=args.candidate
assert hashlib.sha256(source.read_bytes()).hexdigest()=='20d3da8789fc847a4e5450c430321b52350e79f7533bcd43ff48695ffa4c862d'
data=json.loads(source.read_text())
assert not args.output.exists(), 'output directory must be fresh'
out=args.output/'ShielddSecurity'
out.mkdir(parents=True)
entries=data['certificates'];numbers=sorted(map(int,entries))
assert len(numbers)==38 and numbers[-1]==data['modulus']
names={n:f'FieldPrimeNode{i+1:02}' for i,n in enumerate(numbers)}
files={}
for n in numbers:
    item=entries[str(n)];assert item['n']==n
    assert all(q in names and q<n for q in item['factors'])
    residues={r['q']:r for r in item['residues']}
    powers=[]
    for q in item['factors']:
        row=residues[q];assert row['exponent']==(n-1)//q
        powers.append(f"⟨{q}, {row['exponent']}, {row['residue']}⟩")
    dependencies=[names[q] for q in sorted(set(item['factors']))]
    name=names[n]
    body='-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.\n'
    body+='import ShielddSecurity.LucasCertificate\n'
    body+=''.join('import ShielddSecurity.'+dep+'\n' for dep in dependencies)
    body+='\nset_option maxHeartbeats 300000\nset_option maxRecDepth 4096\n\n'
    body+='namespace ShielddSecurity.'+name+'\nopen LucasCertificate\n\n'
    body+=f"def certificate : Certificate := ⟨{n}, {item['base']}, ["+', '.join(powers)+']⟩\n\n'
    body+='theorem checked : certificate.check = true := by decide +kernel\n\n'
    body+=f'theorem prime : Nat.Prime {n} := by\n'
    body+='  change Nat.Prime certificate.n\n  apply certificate_sound certificate _ checked\n'
    body+='  simp [certificate'+''.join(', '+dep+'.prime' for dep in dependencies)+']\n\n'
    body+='end ShielddSecurity.'+name+'\n'
    target=out/(name+'.lean');target.write_bytes(body.encode())
    files[name]={'path':str(target),'sha256':hashlib.sha256(target.read_bytes()).hexdigest(),
                 'n':n,'dependencies':dependencies,'factor_occurrences':len(powers),'distinct_factors':len(dependencies)}
manifest={'candidate_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
          'parent_commit':'e90e824285275bd59eac9fb1f5d173b9e38b0d17','files':files,
          'root':names[data['modulus']],'kernel_run':False,'primality_credit':0}
(out.parent/'manifest.json').write_bytes((json.dumps(manifest,indent=2)+'\n').encode())
print(json.dumps({'files':len(files),'root':manifest['root'],'kernel_run':False,
                 'manifest_sha256':hashlib.sha256((out.parent/'manifest.json').read_bytes()).hexdigest()}))
