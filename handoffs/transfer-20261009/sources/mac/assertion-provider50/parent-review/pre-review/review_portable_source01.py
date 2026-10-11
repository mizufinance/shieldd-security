from pathlib import Path
import hashlib,json,subprocess
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work')
P=W/'mac-assertion-provider50-portable-source01'
J=W/'resumed-orchestration-20261009-01/assertion-provider50-pre-review01'
def pin(p):
 assert p.is_file() and not p.is_symlink(),p
 b=p.read_bytes();return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def check(p,v):
 assert pin(p)=={k:v[k]for k in ['bytes','sha256']},p
before={str(p.relative_to(P)):pin(p)for p in P.rglob('*')if p.is_file()}
m=json.loads((P/'producer-manifest01.json').read_bytes())
for n,v in m.items():check(P/n,v)
e=json.loads((P/'envelope01.json').read_bytes());check(P/'producer-manifest01.json',e['producer']);check(P/'maintained-inventory02.json',e['current_inventory'])
g=json.loads((P/'postseal-guard01.json').read_bytes());check(P/'producer-manifest01.json',g['producer']);check(P/'envelope01.json',g['envelope'])
expected=json.loads((P/'expected-sources01.json').read_bytes());assert len(expected)==90
mix=[]
for name,v in expected.items():
 i=int(name.removeprefix('CapturedAssertions50B'));variant='source04' if i in set(range(25))|{76,89} else 'source06'
 original=W/('mac-assertion-provider50-'+variant)/'source-root/ShielddSecurity'/(name+'.lean')
 check(original,v);mix.append({'name':name,'variant':variant,**pin(original)})
command=json.loads((P/'replay-command01.json').read_bytes())['command'];assert command[:4]==['python3','-I','-B','-S']
report=J/'portable-source-replay01.json';assert not report.exists()
command[command.index('--report')+1]=str(report)
r=subprocess.run(command,capture_output=True,text=True,timeout=60)
assert r.returncode==0,(r.returncode,r.stderr)
after={str(p.relative_to(P)):pin(p)for p in P.rglob('*')if p.is_file()};assert before==after
result={'scope':'Parent independent source-byte replay only; kernel acceptance not asserted','original_sealed_files':len(before),'all_producer_pins_and_postseal_guards_match':True,'maintained_listing_closed':True,'mixed_sources':mix,'source04_count':sum(x['variant']=='source04'for x in mix),'source06_count':sum(x['variant']=='source06'for x in mix),'source_bytes':sum(x['bytes']for x in mix),'replay_report':pin(report),'command':command,'exit':r.returncode,'stderr':r.stderr,'producer_unchanged':True,'original_DATA_provenance':'qualification76342258e7741b9f7863117c4784161329e4be86910bbf57388fcafa589cc9c6 independently matched full RowSpool/SQLite in capture-replay-review01.json; source04/source06 source-row interpretations previously independently reviewed'}
(J/'portable-source-review01.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in ['mixed_sources','command']}))
