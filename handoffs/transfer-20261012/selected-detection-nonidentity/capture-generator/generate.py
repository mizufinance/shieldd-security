from pathlib import Path
import argparse,hashlib,json,os,re
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();out=a.output.resolve();assert not out.exists();pending=out.with_name(out.name+'.pending');assert not pending.exists();sources=pending/'source-root/ShielddSecurity';sources.mkdir(parents=True)
d=json.loads((root/'data.json').read_text());assert d['indices']==[11056,11057] and d['position']==1468
lc=lambda terms:'['+','.join('('+str(c)+','+str(v)+')' for c,v in terms)+']'
row=lambda r:'⟨'+lc(r[0])+','+lc(r[1])+'⟩'
body='noncomputable def entry : Entry := ⟨'+str(d['source_node'])+',false,'+','.join(lc(d[k]) for k in ['left','right','output','auxiliary'])+','+str(d['indices'][0])+',['+','.join(row(r) for r in d['rows'])+']⟩\n'
body+='noncomputable def assertionRows : List Row := ['+row(d['assertion'])+']\n'
s='/- Generated from maintained exact nonidentity capture; edit generator or template. -/\n'+(root/'template.lean.in').read_text().replace('@@DEFINITIONS@@',body)
p=sources/'DetectionNonidentityCapture763.lean';p.write_text(s);(pending/'generation.json').write_text(json.dumps({p.stem:{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'audits':re.findall(r'^#check @([A-Za-z0-9_.]+)',s,re.M)}},indent=2)+'\n');os.replace(pending,out)
print('Generated one exact nonidentity capture module with four audits')
