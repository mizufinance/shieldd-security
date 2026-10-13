from pathlib import Path
import json
root=Path(__file__).resolve().parent
import argparse,os,hashlib
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();assert not a.output.exists();out=a.output.with_name(a.output.name+'.pending');out.mkdir();dest=out/'source-root/ShielddSecurity';dest.mkdir(parents=True)
def showlc(t):return '['+','.join('('+str(c)+','+str(v)+')' for c,v in t)+']'
def showrows(rs):return '['+','.join('⟨'+showlc(a)+','+showlc(b)+'⟩' for a,b in rs)+']'
entries=[]
for e in json.loads((root/'entries.json').read_text()):
 entries.append('⟨'+','.join(showlc(t) for t in e['terms'])+','+str(e['position'])+','+showrows(e['rows'])+'⟩')
s='import ShielddSecurity.PointEqualityAdapter440\nset_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnoncomputable section\nnamespace ShielddSecurity.InitialWindowCapture441\nopen PointEqualityAdapter440\ndef entries : List Entry := ['+','.join(entries)+']\ntheorem checked : entries.all check=true := by decide +kernel\nend ShielddSecurity.InitialWindowCapture441\n'
for n in ['entries','checked']:s+='\nset_option pp.all true in\n#check @ShielddSecurity.InitialWindowCapture441.'+n+'\n#print axioms ShielddSecurity.InitialWindowCapture441.'+n+'\n'
f=dest/'InitialWindowCapture441.lean';f.write_text(s);(out/'generation.json').write_text(json.dumps(dict(sourceSha256=hashlib.sha256(f.read_bytes()).hexdigest(),positions=[2261,2262,3019,3020]))+'\n');os.replace(out,a.output);print('Generated two initial-window point equality entries')
