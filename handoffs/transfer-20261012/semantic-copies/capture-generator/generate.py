from pathlib import Path
import json,argparse,os,hashlib,re
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();assert not a.output.exists();pending=a.output.with_name(a.output.name+'.pending');assert not pending.exists();dst=pending/'source-root/ShielddSecurity';dst.mkdir(parents=True)
entries=json.loads((root/'data.json').read_text());assert [e['position'] for e in entries]==[6057,7460,19301]
lc=lambda terms:'['+','.join('('+str(c)+','+str(v)+')' for c,v in terms)+']'
outputs={}
def emit(name,s):
 p=dst/(name+'.lean');p.write_text('-- GENERATED from maintained exact data/template; do not edit.\n'+s);outputs[name]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),audits=re.findall(r'^#check @([A-Za-z0-9_.]+)',s,re.M))
for i,d in enumerate(entries):
 name='SemanticCopiesCapture800F'+str(i);body='noncomputable def rows : List Row := [⟨'+lc(d['row'][0])+','+lc(d['row'][1])+'⟩]';s=(root/'template.lean.in').read_text().replace('@@NAME@@',name).replace('@@DEFINITION@@',body)
 for k in ['position','left','right']:s=s.replace('@@'+k.upper()+'@@',str(d[k]))
 emit(name,s)
emit('SemanticCopiesCapture800',(root/'root.lean.in').read_text());(pending/'generation.json').write_text(json.dumps(outputs,indent=2)+'\n');os.replace(pending,a.output)
