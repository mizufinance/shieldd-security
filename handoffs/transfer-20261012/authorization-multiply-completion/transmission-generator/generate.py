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
s='import ShielddSecurity.PointEqualityAdapter440\nset_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnoncomputable section\nnamespace ShielddSecurity.TransmissionCapture468\nopen PointEqualityAdapter440\ndef entries : List Entry := ['+','.join(entries)+']\ntheorem checked : entries.all check=true := by decide +kernel\nend ShielddSecurity.TransmissionCapture468\n'
for n in ['entries','checked']:s+='\nset_option pp.all true in\n#check @ShielddSecurity.TransmissionCapture468.'+n+'\n#print axioms ShielddSecurity.TransmissionCapture468.'+n+'\n'
f=dest/'TransmissionCapture468.lean';f.write_text(s);(out/'generation.json').write_text(json.dumps(dict(sourceSha256=hashlib.sha256(f.read_bytes()).hexdigest(),positions=[3013,3014]))+'\n');os.replace(out,a.output);print('Generated transmission equality entry')
