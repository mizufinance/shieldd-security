"""Compile-only generation stage: permit proof consumers of noncomputable tables.
Every input is authenticated. The sole emitted change inserts a noncomputable
section before the first option; all definitions, theorem statements and proof
bodies remain byte-identical. No executable runtime implementation is emitted.
"""
from pathlib import Path
import argparse,json,hashlib,os
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();assert not a.output.exists();a.output.mkdir(parents=True);dst=a.output/'source-root/ShielddSecurity';dst.mkdir(parents=True);records={}
for name,entry in json.loads((root/'inputs.json').read_text()).items():
 p=root/entry['path'];raw=p.read_bytes();assert len(raw)==entry['bytes'] and hashlib.sha256(raw).hexdigest()==entry['sha256'];assert p.stem==name
 assert b'noncomputable section' not in raw
 at=raw.index(b'set_option ');assert at==0 or raw[at-1:at]==b'\n'
 data=raw[:at]+b'noncomputable section\n'+raw[at:];assert data.replace(b'noncomputable section\n',b'',1)==raw;assert len(data)<=262144
 out=dst/(name+'.lean');out.write_bytes(data);records[name]=dict(path=str(out.resolve()),bytes=len(data),sha256=hashlib.sha256(data).hexdigest(),original=entry)
(a.output/'generation.json').write_text(json.dumps(records,indent=2)+'\n');print(json.dumps(dict(modules=len(records),change='noncomputable section only')))
