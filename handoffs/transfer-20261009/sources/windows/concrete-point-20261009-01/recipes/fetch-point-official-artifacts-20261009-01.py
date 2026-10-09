from pathlib import Path
import hashlib,json,os,re,shutil,signal,subprocess,time,urllib.request

local=Path('/mnt/c/src/shieldd-transfer-handoffs')
stage=local/'point-artifact-stage-20261009-01'
assert not stage.exists();stage.mkdir()
os.setpgid(0,0)
pid=os.getpid();startTicks=Path(f'/proc/{pid}/stat').read_text().split()[21]
(stage/'owned-process.json').write_text(json.dumps({'pid':pid,'pgid':os.getpgrp(),'start_ticks':startTicks,'script':str(Path(__file__).resolve())}))
deadline=time.monotonic()+235
sourceRoot=Path('/root/.cache/shieldd-security-verification/b0f7e8b/circuits/.lake/packages')
toolchain=Path('/root/.cache/shieldd-security-lean/lean-4.30.0-linux')
availability=json.loads((local/'point-official-artifact-inspection-20261009-02.json').read_text())
inspection=json.loads((local/'edwards-point-closure-inspection-20261009-01.json').read_text())
limit=2*1024**3;reserve=16*1024**2
missing=[v for v in availability['records'] if not v['available']]
modules=sorted({v['relative'].split('.olean',1)[0].removesuffix('.ir').replace('/','.') for v in missing})
assert len(modules)==36
projected=availability['projected_final_bytes']+len(modules)*reserve
assert projected<=limit and shutil.disk_usage('/mnt/c/src').free>4*1024**3
def run(args,**kwargs):
    remaining=deadline-time.monotonic();assert remaining>0
    return subprocess.run(args,check=True,timeout=remaining,**kwargs)
env=os.environ.copy();env['PATH']=str(toolchain/'bin')+':'+env.get('PATH','')
env['LEAN_NUM_THREADS']='1'
env['LEAN_SRC_PATH']=':'.join(str(p) for p in sourceRoot.iterdir() if p.is_dir())
env['LEAN_PATH']=':'.join(str(p/'.lake/build/lib/lean') for p in sourceRoot.iterdir() if p.is_dir())
version=run([str(toolchain/'bin/lean'),'--version'],capture_output=True,text=True).stdout
assert 'version 4.30.0' in version
for name,rev in availability['packages'].items():
    p=sourceRoot/name
    assert run(['git','-C',str(p),'rev-parse','HEAD'],capture_output=True,text=True).stdout.strip()==rev
    assert not run(['git','-C',str(p),'status','--porcelain','--untracked-files=no'],capture_output=True,text=True).stdout.strip()
catalog=run([str(toolchain/'bin/lean'),'-j1','-M','1536','--run',str(local/'PointCacheHashCatalog01.lean'),*modules],
            cwd=sourceRoot/'mathlib',env=env,capture_output=True,text=True).stdout
(stage/'catalog.txt').write_text(catalog)
keys={}
for line in catalog.splitlines():
    if match:=re.fullmatch(r'(Mathlib[\w.]+) ([0-9a-f]{16}\.ltar)',line):keys[match[1]]=match[2]
assert set(keys)==set(modules),(len(keys),len(modules),catalog[:1500])
archives=stage/'archives';archives.mkdir();unpack=stage/'unpacked';unpack.mkdir()
collected=[];downloaded=[];artifactBytes=availability['projected_final_bytes']
for module in modules:
    archive=archives/keys[module];existing=Path('/root/.cache/mathlib')/keys[module]
    if existing.exists():shutil.copyfile(existing,archive);origin='already cached official archive'
    else:
        url='https://lakecache.blob.core.windows.net/mathlib4/f/'+keys[module]
        with urllib.request.urlopen(url,timeout=min(20,max(1,deadline-time.monotonic()))) as response, archive.open('wb') as out:
            count=0
            while chunk:=response.read(1024**2):
                count+=len(chunk);assert count<=reserve,'archive exceeds bounded download planning reserve'
                assert time.monotonic()<deadline;out.write(chunk)
        origin=url
    downloaded.append({'module':module,'archive':keys[module],'sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'bytes':archive.stat().st_size,'origin':origin})
    assert artifactBytes+reserve<=limit,'remaining qualification budget exhausted'
    run([str(toolchain/'bin/leantar'),'-x','--jobs','1',str(archive)],cwd=unpack,env=env,capture_output=True,text=True)
    for record in [v for v in missing if v['relative'].startswith(module.replace('.','/')+'.')]:
        p=unpack/'.lake/build/lib/lean'/record['relative'];assert p.is_file(),p
        n=p.stat().st_size;artifactBytes+=n;assert artifactBytes<=limit
        collected.append({'relative':record['relative'],'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':n})
    assert time.monotonic()<deadline
assert len(collected)==144
available=[v for v in availability['records'] if v['available']]
for v in available:assert hashlib.sha256(Path(v['path']).read_bytes()).hexdigest()==v['sha256']
for item in inspection['sources'].values():
    windows=item['source'].replace('\\','/');source=Path('/mnt/c/'+windows[3:])
    assert hashlib.sha256(source.read_bytes()).hexdigest()==item['sha256']
receipt={'kind':'Qualified exact-source official artifact retrieval, zero proof/import credit','packages':availability['packages'],
 'additional_artifacts':available+collected,'archives':downloaded,'preflight_projected_bytes':projected,
 'projection_disposition':'Planning reserve16MiB per missing module; actual mandatory bytes independently checked before qualification',
 'final_qualified_closure_bytes':artifactBytes,'limit_bytes':limit,'threads':1,'finite_seconds':235,
 'toolchain_version':version.strip(),'toolchain_hashes':{name:hashlib.sha256((toolchain/'bin'/name).read_bytes()).hexdigest() for name in ['lean','leantar']},
 'hash_catalog_source_sha256':hashlib.sha256((local/'PointCacheHashCatalog01.lean').read_bytes()).hexdigest(),'kernel_run':False,'proof_credit':0}
(stage/'receipt.json').write_bytes((json.dumps(receipt,indent=2)+'\n').encode())
print(json.dumps({k:receipt[k] for k in ['kind','preflight_projected_bytes','final_qualified_closure_bytes','limit_bytes','kernel_run','proof_credit']}))
