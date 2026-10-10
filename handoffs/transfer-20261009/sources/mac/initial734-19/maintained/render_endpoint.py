"""Pinned endpoint-only generation; no capture/executor."""
from pathlib import Path
import sys,importlib.util,hashlib,json
H=Path(__file__).resolve().parent
if not(sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site and not sys.flags.optimize):raise ValueError('flags')
p=H/'generate19.py';spec=importlib.util.spec_from_file_location('gen',p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
R=H.parents[2];data=R/'work/mac-initial734-completion19-source01/selected-data01.json.zlib';d=m.bounded_json(data)
for pin in d['source_only'].values():m.require(m.rec(pin['path'])==pin,'frozen input')
a=m.render(d);m.require(m.render(d)==a,'in memory replay');out=H.parent/'source-root/ShielddSecurity';out.mkdir(parents=True,exist_ok=False)
n='CapturedInitial73419Completion01';(out/(n+'.lean')).write_bytes(a[n])
n='CapturedInitial73419Completion01'
print(json.dumps({'source':m.rec(out/(n+'.lean'))}))
