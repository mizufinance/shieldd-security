"""Read-only check of original source bytes against the accepted composition pool."""
from pathlib import Path
import argparse,hashlib,json,re
p=argparse.ArgumentParser();p.add_argument('--packet',required=True,type=Path);p.add_argument('--composition',required=True,type=Path);p.add_argument('--report',required=True,type=Path);a=p.parse_args()
def pin(path):
 assert path.is_file()and not path.is_symlink(),path
 b=path.read_bytes();return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
P=a.packet;mb=(P/'manifest.json').read_bytes();m=json.loads(mb)
assert pin(a.composition)=={k:m['composition_manifest'][k]for k in ['bytes','sha256']}
c=json.loads(a.composition.read_bytes());selected={x['module']:x for x in c['selected']};assert len(selected)==m['composition_selected_count']==437
assert m['source_count']==len(m['sources'])==22 and not m['certification']
assert pin(P/'assemble.py')=={k:m['recipe'][k]for k in ['bytes','sha256']}
names={x['module']for x in m['sources']};assert len(names)==22
observed={str(x.relative_to(P))for x in P.rglob('*')if x.is_file()};expected={'manifest.json','assemble.py'}|{x['archive_path']for x in m['sources']};assert observed==expected
report=[]
for s in m['sources']:
 name=s['module'];assert s['original_selected_record']==selected[name]
 assert s['archive_path']=='source/ShielddSecurity/'+name+'.lean'
 assert {k:s[k]for k in ['bytes','sha256']}=={k:selected[name]['source'][k]for k in ['bytes','sha256']}
 file=P/s['archive_path'];assert pin(file)=={k:s[k]for k in ['bytes','sha256']}
 imports=re.findall(r'^import ([\w.]+)\s*$',file.read_text(),re.M)
 custom=[n.removeprefix('ShielddSecurity.')for n in imports if n.startswith('ShielddSecurity.')]
 assert set(custom)<=set(selected),(name,custom)
 report.append({'module':name,**pin(file),'custom_imports':custom})
r={'kind':'EXACT_ORIGINAL_OWNED_SOURCE_SUPPLEMENT_PARENT_REVIEW','scope':'Source identity/transport only; no normalization, fresh kernel replay, merged source choice or certification','sources':report,'source_count':len(report),'source_bytes':sum(s['bytes']for s in report),'composition':pin(a.composition),'producer_manifest':pin(P/'manifest.json'),'recipe':pin(P/'assemble.py'),'packet_closed':True,'all_original_selected_records_exact':True,'all_custom_imports_in_accepted_pool':True,'full_transfer':'OPEN'}
with a.report.open('x')as f:f.write(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:v for k,v in r.items()if k!='sources'}))
