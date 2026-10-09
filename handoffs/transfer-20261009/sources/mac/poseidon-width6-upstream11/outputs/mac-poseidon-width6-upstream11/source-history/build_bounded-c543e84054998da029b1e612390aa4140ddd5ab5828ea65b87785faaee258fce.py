import hashlib,json,os,re,shutil,signal,subprocess,sys,time
from pathlib import Path
from freeze_external import freeze_external
from audit_log import validate

STAGE=Path(__file__).resolve().parent
ROOT=STAGE.parents[1]
PROJECT=STAGE/'project'
OUT=ROOT/'outputs/mac-poseidon-width6-upstream11'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
packet=json.loads((OUT/'input-packet01.json').read_text())['packet']
args=sys.argv[1:]
heap=2048 if args[:1]==['--heap2048'] else 1536
if heap==2048:args=args[1:]
modules=packet['topological_import_order'] if args==['dependencies'] else args
assert modules
records=[]
guard_sources={p.name:sha(p) for p in [Path(__file__),STAGE/'freeze_external.py',STAGE/'audit_log.py']}
def code_without_comments(text):
    result=[];i=0;depth=0
    while i<len(text):
        if text[i:i+2]=='/-':depth+=1;i+=2
        elif depth and text[i:i+2]=='-/':depth-=1;i+=2
        elif not depth and text[i:i+2]=='--':
            end=text.find('\n',i);i=len(text) if end<0 else end
        else:
            if not depth or text[i]=='\n':result.append(text[i])
            i+=1
    assert depth==0,'unclosed Lean comment'
    return ''.join(result)
def names_in_source(source, command):
    namespace=''; stack=[]; result=[]
    for line in source.read_text().splitlines():
        match=re.match(r'^namespace (\S+)',line)
        if match:
            stack.append(namespace)
            namespace=(namespace+'.' if namespace else '')+match.group(1)
        if re.match(r'^end(?: |$)',line):namespace=stack.pop() if stack else ''
        match=re.match(command,line)
        if match:
            name=match.group(1)
            result.append(name if name.startswith('ShielddSecurity.') else namespace+'.'+name)
    assert len(result)==len(set(result)), 'duplicate source audit name'
    return result

def imported_identities(source):
    result={}; pending=[source]; seen=set()
    while pending:
        current=pending.pop()
        if current in seen:continue
        seen.add(current)
        text=current.read_text()
        assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',code_without_comments(text))
        for name in re.findall(r'^import (ShielddSecurity\.\S+)',text,re.M):
            path=PROJECT/(name.replace('.','/')+'.lean')
            obj=PROJECT/'.lake/build/lib/lean'/(name.replace('.','/')+'.olean')
            assert path.is_file() and obj.is_file(),name
            short=name.removeprefix('ShielddSecurity.')
            matching=[json.loads(x.read_text()) for x in OUT.glob(f'build-{short}-*.json')]
            assert any(x['status']=='passed' and x['source_sha256']==sha(path)
                       and x['object_sha256']==sha(obj) for x in matching), 'unbound import: '+name
            result[name]=dict(source_sha256=sha(path),object_sha256=sha(obj))
            pending.append(path)
    result['package']=dict(lakefile_sha256=sha(PROJECT/'lakefile.lean'),
        lake_manifest_sha256=sha(PROJECT/'lake-manifest.json'),
        toolchain_sha256=sha(PROJECT/'lean-toolchain'))
    result['mathlib_revision']=subprocess.check_output(['git','rev-parse','HEAD'],
        cwd=PROJECT/'.lake/packages/mathlib',text=True).strip()
    assert result['mathlib_revision']=='c5ea00351c28e24afc9f0f84379aa41082b1188f'
    official=freeze_external(PROJECT,seen)
    payload=json.dumps(official,sort_keys=True,separators=(',',':'))+'\n'
    identity=hashlib.sha256(payload.encode()).hexdigest()
    manifest=OUT/f'official-imports-{identity[:16]}.json'
    if manifest.exists():assert manifest.read_text()==payload,'official manifest collision/mutation'
    else:manifest.write_text(payload)
    result['official_import_closure']=dict(manifest_sha256=identity,
        manifest_file=manifest.name,modules=official['modules'],files=len(official['files']),
        before_after_equality_required=True)
    return result

for name in modules:
    source=PROJECT/'ShielddSecurity'/f'{name}.lean'
    identity=sha(source)
    if name in packet['topological_import_order']:
        assert identity==packet['files'][f'circuits/ShielddSecurity/{name}.lean']['sha256']
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',code_without_comments(source.read_text()))
    frozen_imports=imported_identities(source)
    expected_axioms=names_in_source(source,r'^#print axioms (\S+)')
    expected_checks=names_in_source(source,r'^#check @?(\S+)')
    index=1
    while (OUT/f'build-{name}-{index:02d}.log').exists(): index+=1
    log=OUT/f'build-{name}-{index:02d}.log'
    dest=PROJECT/'.lake/build/lib/lean/ShielddSecurity'/f'{name}.olean'
    dest.parent.mkdir(parents=True,exist_ok=True)
    command=['lake','+leanprover/lean4:v4.30.0','env','lean','-j1',f'-M{heap}','-o',str(dest),str(source)]
    result=dict(module=name,source_sha256=identity,command=command,status='running',timeout_seconds=240,
                process_group_rss_limit_bytes=4*1024**3,lean_heap_limit_MiB=heap,
                frozen_imports=frozen_imports,expected_axiom_names=expected_axioms,
                expected_signature_names=expected_checks,guard_sources_sha256=guard_sources)
    receipt=OUT/f'build-{name}-{index:02d}.json'
    receipt.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(start=name,attempt=index)),flush=True)
    started=time.monotonic();peak=0;min_memory=100;min_disk=shutil.disk_usage(PROJECT).free
    with log.open('w') as output:
        proc=subprocess.Popen(command,cwd=PROJECT,env=dict(os.environ,LEAN_NUM_THREADS='1'),
                              stdout=output,stderr=subprocess.STDOUT,start_new_session=True)
        while proc.poll() is None:
            pressure=subprocess.check_output(['memory_pressure'],text=True)
            match=re.search(r'System-wide memory free percentage: (\d+)%',pressure)
            memory=int(match.group(1)) if match else 0
            processes=subprocess.check_output(['ps','-axo','pgid=,rss='],text=True)
            rss=sum(int(line.split()[1])*1024 for line in processes.splitlines()
                    if len(line.split())==2 and int(line.split()[0])==proc.pid)
            disk=shutil.disk_usage(PROJECT).free
            peak=max(peak,rss);min_memory=min(min_memory,memory);min_disk=min(min_disk,disk)
            reason=None
            if time.monotonic()-started>240:reason='module time bound'
            elif rss>4*1024**3:reason='process group RSS bound'
            elif memory<15:reason='memory pressure guard'
            elif disk<2*1024**3:reason='free disk guard'
            if reason:
                os.killpg(proc.pid,signal.SIGTERM)
                try:proc.wait(timeout=5)
                except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
                result.update(status='interrupted',reason=reason);break
            time.sleep(.5)
    text=log.read_text()
    result.update(exit=proc.returncode,seconds=time.monotonic()-started,peak_group_rss_bytes=peak,
        minimum_memory_free_percent=min_memory,minimum_disk_free_bytes=min_disk,log_sha256=sha(log))
    if result['status']=='running':result['status']='passed' if proc.returncode==0 else 'failed'
    if sha(source)!=identity or 'sorryAx' in text or 'error:' in text:result['status']='failed'
    try:
        assert {name:sha(STAGE/name) for name in guard_sources}==guard_sources,'guard source changed'
        assert imported_identities(source)==frozen_imports,'import identity changed'
        if proc.returncode==0:
            result.update(validate(text,expected_axioms,expected_checks))
        else:
            result['status']='failed' if result['status']!='interrupted' else result['status']
            if not result.get('reason'):result['reason']='Lean process exit '+str(proc.returncode)
            result['failure_observation']=[line[:500] for line in text.splitlines() if 'error' in line or 'exception' in line][:3]
    except (AssertionError,OSError) as error:
        result.update(status='failed',reason=str(error))
    result.update(object_sha256=sha(dest) if dest.exists() else None)
    receipt.write_text(json.dumps(result,indent=2)+'\n');records.append(result)
    print(json.dumps({k:result.get(k) for k in ['module','status','exit','seconds',
        'peak_group_rss_bytes','axiom_audits','source_sha256','object_sha256','reason']}),flush=True)
    if result['status']!='passed':sys.exit(1)
name='dependencies' if args==['dependencies'] else '-'.join(modules)
if len(name)>120:name='batch-'+hashlib.sha256(name.encode()).hexdigest()[:16]
target=OUT/f'{name}-build-{int(time.time())}.json'
target.write_text(json.dumps(dict(status='passed',modules=records),indent=2)+'\n')
