"""Finite DATA checks of exact-named signature extraction, no Lean execution."""
import hashlib,json,runpy
from pathlib import Path
S=Path(__file__).resolve().parent
extract=runpy.run_path(str(S/'extract_audits.py'))['extract']
name='ShielddSecurity.ParserProbe.theorem'
signature='@'+name+' : True'
digest=hashlib.sha256(signature.encode()).hexdigest()
report="'"+name+"' depends on axioms: [propext,\n Classical.choice, Quot.sound]"
base=signature+'\n'+report+'\n'
controls=[]
for label,prefix in [('plain',''),('preceding_warning','file.lean:1:0: warning: unused variables\n consider omit [CharP F p]\n\n')]:
    full,axioms,h=extract(prefix+base,name,digest)
    assert full==signature and h==digest and axioms==report.removeprefix("'"+name+"' ")
    controls.append(dict(control=label,status='accepted',scope='exact named type, wrapped standard axiom report'))
for label,text,expected in [
    ('duplicate_signature',base+base,digest),
    ('missing_report',signature+'\n',digest),
    ('missing_signature',report+'\n',digest),
    ('wrong_hash',base,'0'*64),
    ('unexpected_axiom',signature+'\n'+"'"+name+"' depends on axioms: [sorryAx]\n",digest)]:
    try:extract(text,name,expected)
    except AssertionError as error:controls.append(dict(control=label,status='refused',reason=str(error)))
    else:raise AssertionError('failed to refuse '+label)
p=S/'parser-controls01.json';assert not p.exists();p.write_text(json.dumps(dict(status='passed',controls=controls,kernel_runs=0,extractor_sha256=hashlib.sha256((S/'extract_audits.py').read_bytes()).hexdigest()),indent=2)+'\n')
print(json.dumps(dict(status='passed',positive=2,refusals=5,receipt_sha256=hashlib.sha256(p.read_bytes()).hexdigest())))
