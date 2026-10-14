from pathlib import Path
import json,argparse,os,hashlib,re
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();assert not a.output.exists();pending=a.output.with_name(a.output.name+'.pending');assert not pending.exists();dst=pending/'source-root/ShielddSecurity';dst.mkdir(parents=True)
d=json.loads((root/'data.json').read_text());assert d['position']==7610
lc=lambda terms:'['+','.join('('+str(c)+','+str(v)+')' for c,v in terms)+']'
body='noncomputable def rows : List Row := [⟨'+lc(d['row'][0])+','+lc(d['row'][1])+'⟩]'
s='-- GENERATED from maintained data and template; do not edit.\n'+(root/'template.lean.in').read_text().replace('@@DEFINITION@@',body)
p=dst/'VolumeTimestampCapture792.lean';p.write_text(s);(pending/'generation.json').write_text(json.dumps({p.stem:dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),audits=re.findall(r'^#check @([A-Za-z0-9_.]+)',s,re.M))},indent=2)+'\n');os.replace(pending,a.output)
