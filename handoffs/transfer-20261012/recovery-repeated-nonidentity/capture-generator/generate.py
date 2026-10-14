from pathlib import Path
import argparse,hashlib,json,os,re
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();assert not a.output.exists();pending=a.output.with_name(a.output.name+'.pending');assert not pending.exists();dst=pending/'source-root/ShielddSecurity';dst.mkdir(parents=True)
entries=json.loads((root/'data.json').read_text());assert [e['position'] for e in entries]==[6052,7455]
lc=lambda terms:'['+','.join('('+str(c)+','+str(v)+')' for c,v in terms)+']'
row=lambda r:'⟨'+lc(r[0])+','+lc(r[1])+'⟩'
outputs={}
def emit(name,s):
 p=dst/(name+'.lean');p.write_text('-- GENERATED from data.json and maintained templates. Do not hand edit.\n'+s);outputs[name]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),audits=re.findall(r'^#check @([A-Za-z0-9_.]+)',s,re.M))
for i,d in enumerate(entries):
 name='RecoveryInverseCapture779F'+str(i)
 body='noncomputable def entry : Entry := ⟨'+str(d['source_node'])+',false,'+','.join(lc(d[k]) for k in ['left','right','output','auxiliary'])+','+str(d['indices'][0])+',['+','.join(row(r) for r in d['rows'])+']⟩\n'
 body+='noncomputable def assertionRows : List Row := ['+row(d['assertion'])+']\n'
 s=(root/'capture.lean.in').read_text().replace('@@DEFINITIONS@@',body).replace('@@NAME@@',name).replace('@@POSITION@@',str(d['position'])).replace('@@OUTPUT@@',str(d['output'][0][0])).replace('@@HINT@@',str(d['left'][0][0])).replace('@@OPERAND@@',str(d['right'][0][0]));emit(name,s)
emit('RecoveryInverseCapture779',(root/'root.lean.in').read_text());(pending/'generation.json').write_text(json.dumps(outputs,indent=2)+'\n');os.replace(pending,a.output)
