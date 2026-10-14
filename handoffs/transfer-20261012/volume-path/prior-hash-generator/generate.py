from pathlib import Path
import argparse,json,hashlib,shutil,subprocess,sys,os,re
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--repository',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();out=a.output.resolve();assert not out.exists();pending=out.with_name(out.name+'.pending');assert not pending.exists();pending.mkdir();dest=pending/'source-root/ShielddSecurity';dest.mkdir(parents=True)
config=json.loads((root/'original-generators.json').read_text());inventory={}
for pkg,files in config.items():
 base=a.repository.resolve()/'handoffs/transfer-20261012'/pkg/'hash-generator'
 assert {p.name for p in base.iterdir() if p.is_file()}==set(files)
 for name,identity in files.items():
  data=(base/name).read_bytes();assert len(data)==identity['bytes'] and hashlib.sha256(data).hexdigest()==identity['sha256']
 patched=pending/(pkg+'-generator');shutil.copytree(base,patched);shutil.copy2(root/(pkg+'.lean.in'),patched/'composition.lean.in')
 generated=pending/(pkg+'-generated');subprocess.run([sys.executable,'-B','-I','-S',str(patched/'generate.py'),'--output',str(generated)],check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 for p in (generated/'source-root/ShielddSecurity').glob('*.lean'):
  if 'Composition' not in p.stem:continue
  assert p.stem not in inventory;shutil.copy2(p,dest/p.name);inventory[p.stem]=dict(bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),audits=re.findall(r'^#check @([A-Za-z0-9_.]+)',p.read_text(),re.M))
 shutil.rmtree(patched);shutil.rmtree(generated)
assert len(inventory)==9
(pending/'generation.json').write_text(json.dumps(inventory,indent=2,sort_keys=True)+'\n');os.replace(pending,out);print(json.dumps(dict(modules=len(inventory),audits=sum(len(v['audits']) for v in inventory.values()))))
