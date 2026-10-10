"""SOURCE-prepared runner, disabled until external explicit KERNEL admission."""
import argparse,hashlib,json,os,re,shutil,signal,subprocess,sys,time
from pathlib import Path
assert sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site,'use -I -B -S'
S=Path(__file__).resolve().parent
parser=argparse.ArgumentParser()
for name in ['inventory','source-inventory','imports','workspace','output-dir','root','admission']:
    parser.add_argument('--'+name,type=Path,required=True)
for name in ['inventory-sha256','source-inventory-sha256','admission-sha256','module']:
    parser.add_argument('--'+name,required=True)
args=parser.parse_args();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(args.inventory)==args.inventory_sha256 and sha(args.source_inventory)==args.source_inventory_sha256
inventory=json.loads(args.inventory.read_text())
# Close and hash every maintained entry BEFORE importing any local helper.
assert {p.name for p in S.iterdir()}==set(inventory['maintained_files'])
for name,entry in inventory['maintained_files'].items():
    path=S/name
    assert path.is_file() and not path.is_symlink() and sha(path)==entry['sha256'] and path.stat().st_size==entry['bytes']
assert sha(Path(__file__))==inventory['maintained_files'][Path(__file__).name]['sha256']
sys.path.insert(0,str(S))
from source_contract import closed,safe_lean,audit_names
from freeze_external import freeze_external
from audit_log import validate
from owned_process import cleanup_owned
closed(S,inventory,Path(__file__))
sources=json.loads(args.source_inventory.read_text())
assert sources['status']=='SOURCE ONLY; no successor proof accepted'
allowed=sources['successor_topological_order'];assert args.module in allowed
assert sha(args.imports)==sources['probe_imports_sha256']
inherited=json.loads(args.imports.read_text())['modules']
# ALL frozen prior attempt receipts MUST remain present and hashed; changing receipt
# directory is forbidden, so failure retry cannot reset cumulative accounting.
assert args.output_dir.resolve()==(args.root/sources['prior_receipt_directory']).resolve(),'wrong prior receipt directory'
for name,entry in sources['prior_receipt_records'].items():
    path=args.output_dir/name
    assert path.is_file() and not path.is_symlink() and sha(path)==entry['sha256'] and path.stat().st_size==entry['bytes'],'prior receipt identity missing/changed: '+name
args.output_dir.mkdir(parents=True,exist_ok=True)
indices=1
while (args.output_dir/f'build-{args.module}-{indices:02d}.json').exists():indices+=1
receipt=args.output_dir/f'build-{args.module}-{indices:02d}.json'
log=receipt.with_suffix('.log')
result={'module':args.module,'status':'prelaunch','command_started':False,'fresh_credit':0,
        'source_inventory_sha256':sha(args.source_inventory),'maintained_inventory_sha256':sha(args.inventory),
        'admission_sha256':None,'timeout_seconds':240,'process_group_rss_limit_bytes':4*1024**3,'lean_heap_limit_MiB':2048}
def write():receipt.write_text(json.dumps(result,indent=2)+'\n')
def prior_runs():return [json.loads(p.read_text()) for p in args.output_dir.glob('build-*.json') if p!=receipt]
def memory_free():
    text=subprocess.check_output(['memory_pressure'],text=True)
    return int(re.search(r'System-wide memory free percentage: (\d+)%',text).group(1))
def heavy_processes():
    text=subprocess.check_output(['ps','-axo','pid=,comm='],text=True)
    return [x.strip() for x in text.splitlines() if Path(x.split(maxsplit=1)[1]).name in {'lake','lean','cargo','rustc'}]
def own_byte_size():
    names=set(sources['modules']);total=0
    for name in names:
        p=args.workspace/'ShielddSecurity'/f'{name}.lean'
        if p.exists():total+=p.stat().st_size
        objects=args.workspace/'.lake/build/lib/lean/ShielddSecurity'
        total+=sum(p.stat().st_size for p in objects.glob(name+'.*') if p.is_file())
    return total
def imports_frozen(source):
    pending=[source];seen=set();identities={}
    while pending:
        current=pending.pop()
        if current in seen:continue
        seen.add(current);safe_lean(current.read_text())
        for name in re.findall(r'^import ShielddSecurity\.(\S+)',current.read_text(),re.M):
            path=args.workspace/'ShielddSecurity'/f'{name}.lean'
            obj=args.workspace/'.lake/build/lib/lean/ShielddSecurity'/f'{name}.olean'
            assert path.is_file() and obj.is_file(),'missing inherited/fresh artifact: '+name
            if name in inherited:
                entry=inherited[name];prior=args.root/entry['receipt_path']
                assert sha(prior)==entry['receipt_sha256'];observed=json.loads(prior.read_text())
                assert observed['status']=='passed' and sha(path)==entry['source_sha256']==observed['source_sha256']
                assert sha(obj)==entry['object_sha256']==observed['object_sha256']
                ancestry={'classification':'inherited ZERO fresh execution','receipt_path':entry['receipt_path'],'receipt_sha256':sha(prior)}
            else:
                assert name in sources['modules'] and sha(path)==sources['modules'][name]['sha256']
                if name in sources['accepted_probes']:
                    prior=args.root/sources['accepted_probes'][name]['receipt_path'];observed=json.loads(prior.read_text())
                    assert sha(prior)==sources['accepted_probes'][name]['receipt_sha256']
                else:
                    possible=[p for p in args.output_dir.glob(f'build-{name}-*.json') if (r:=json.loads(p.read_text()))['status']=='passed' and r.get('source_sha256')==sha(path) and r.get('object_sha256')==sha(obj)]
                    assert possible,'unbound successor import: '+name
                    prior=sorted(possible)[-1];observed=json.loads(prior.read_text())
                assert observed['status']=='passed' and observed['source_sha256']==sha(path) and observed['object_sha256']==sha(obj)
                ancestry={'classification':'accepted probe reused' if name in sources['accepted_probes'] else 'fresh bounded successor',
                          'receipt_path':str(prior),'receipt_sha256':sha(prior)}
            parts={part.name:sha(part) for suffix in ['.olean.private','.olean.server','.ilean'] if (part:=obj.with_suffix(suffix)).exists()}
            if name in inherited:assert parts==inherited[name]['copied_extra_parts'],'inherited split object mismatch: '+name
            identities[name]={'source_sha256':sha(path),'object_sha256':sha(obj),'parts':parts,**ancestry};pending.append(path)
    identities['package']={p:sha(args.workspace/p) for p in ['lakefile.lean','lake-manifest.json','lean-toolchain']}
    assert identities['package']==sources['package']
    official=freeze_external(args.workspace,seen)
    payload=json.dumps(official,sort_keys=True,separators=(',',':'))+'\n';digest=hashlib.sha256(payload.encode()).hexdigest()
    path=args.output_dir/f'official-imports-{digest[:16]}.json'
    if path.exists():assert path.read_text()==payload
    else:path.write_text(payload)
    identities['official_import_closure']={'manifest_file':path.name,'manifest_sha256':digest,'modules':official['modules'],'files':len(official['files'])}
    return identities
proc=None;started=None;peak=0;min_memory=100;min_disk=None
try:
    # Explicit parent admission must bind these exact SOURCE identities. The
    # SOURCE-generation-only authorization is deliberately insufficient here.
    assert args.admission.is_file() and sha(args.admission)==args.admission_sha256,'missing exact kernel admission'
    admission=json.loads(args.admission.read_text());assert admission['kernel_admission'] is True
    assert admission['source_inventory_sha256']==sha(args.source_inventory) and admission['maintained_inventory_sha256']==sha(args.inventory)
    assert args.module in admission['modules'];result['admission_sha256']=sha(args.admission)
    prior=prior_runs();assert len(prior)+2<60,'ALLstage attempt ceiling'
    consumed=sum(x.get('seconds',0) for x in prior if x.get('command_started'))+6.871448499994585
    assert consumed<1200,'ALLstage cumulative Lean wall budget'
    assert own_byte_size()<=512*1024**2,'new source+object byte ceiling'
    assert not heavy_processes(),'heavy lane occupied'
    assert memory_free()>=15 and shutil.disk_usage(args.workspace).free>=2*1024**3,'memory/disk prelaunch refusal'
    # Bind ALL generated modules, not only the next target, before each build.
    for name,entry in sources['modules'].items():
        path=args.workspace/'ShielddSecurity'/f'{name}.lean'
        assert path.is_file() and not path.is_symlink() and sha(path)==entry['sha256'] and path.stat().st_size==entry['bytes'],'source inventory mismatch: '+name
    source=args.workspace/'ShielddSecurity'/f'{args.module}.lean';safe_lean(source.read_text())
    result['source_sha256']=sha(source);result['source_bytes']=source.stat().st_size
    result['frozen_imports']=imports_frozen(source)
    axiom_names=audit_names(source,r'^#print axioms (\S+)');signature_names=audit_names(source,r'^#check @?(\S+)')
    assert sorted(axiom_names)==sorted(signature_names)
    result.update(expected_axiom_names=axiom_names,expected_signature_names=signature_names)
    dest=args.workspace/'.lake/build/lib/lean/ShielddSecurity'/f'{args.module}.olean';dest.parent.mkdir(parents=True,exist_ok=True)
    command=['lake','+leanprover/lean4:v4.30.0','env','lean','-j1','-M2048','-o',str(dest),str(source)]
    result.update(command=command,status='prelaunch',command_started=False,environment={'LEAN_NUM_THREADS':'1'},guard_sources_sha256={k:v['sha256'] for k,v in inventory['maintained_files'].items()});write()
    started=time.monotonic();peak=0;min_memory=100;min_disk=shutil.disk_usage(args.workspace).free;heartbeat=0
    with log.open('x') as output:
        try:
            proc=subprocess.Popen(command,cwd=args.workspace,env=dict(os.environ,LEAN_NUM_THREADS='1'),stdout=output,stderr=subprocess.STDOUT,start_new_session=True)
            result.update(status='running',command_started=True,owned_process_group=proc.pid);write()
            while proc.poll() is None:
                memory=memory_free();disk=shutil.disk_usage(args.workspace).free
                ps=subprocess.check_output(['ps','-axo','pgid=,rss='],text=True)
                rss=sum(int(p[1])*1024 for line in ps.splitlines() if len(p:=line.split())==2 and int(p[0])==proc.pid)
                elapsed=time.monotonic()-started;peak=max(peak,rss);min_memory=min(min_memory,memory);min_disk=min(min_disk,disk)
                reason=('module time bound' if elapsed>240 else 'cumulative Lean wall bound' if consumed+elapsed>1200 else
                        'RSS bound' if rss>4*1024**3 else 'memory bound' if memory<15 else 'disk bound' if disk<2*1024**3 else
                        'source+object growth bound' if own_byte_size()>512*1024**2 else None)
                if reason:
                    result.update(status='interrupted',reason=reason);break
                if elapsed//30>heartbeat:
                    heartbeat=int(elapsed//30);print(json.dumps({'heartbeat':args.module,'seconds':elapsed,'RSS_bytes':rss}),flush=True)
                time.sleep(.5)
        finally:
            # All paths, including unexpected monitoring errors/KeyboardInterrupt,
            # clean up only the session created by this runner before releasing lane.
            if proc is not None:result['owned_cleanup']=cleanup_owned(proc)
    result.update(exit=proc.returncode,seconds=time.monotonic()-started,peak_group_rss_bytes=peak,
                  minimum_memory_free_percent=min_memory,minimum_disk_free_bytes=min_disk,log_sha256=sha(log))
    assert result['owned_cleanup']['leader_reaped'] and not result['owned_cleanup']['errors'],'owned process cleanup failed'
    if result['status']=='running':result['status']='passed' if proc.returncode==0 else 'failed'
    assert sha(source)==result['source_sha256'];closed(S,inventory,Path(__file__))
    assert sha(args.inventory)==args.inventory_sha256 and sha(args.source_inventory)==args.source_inventory_sha256
    assert imports_frozen(source)==result['frozen_imports'],'source/import identity changed'
    if proc.returncode==0:result.update(validate(log.read_text(),axiom_names,signature_names))
    result.update(object_sha256=sha(dest) if dest.exists() else None,object_bytes=dest.stat().st_size if dest.exists() else None)
    assert own_byte_size()<=512*1024**2
    result['fresh_credit']=1 if result['status']=='passed' else 0
except BaseException as error:
    result.update(status='failed' if result['command_started'] else 'admission_refused',reason=str(error),error_type=type(error).__name__,fresh_credit=0)
finally:
    # Backup cleanup covers errors raised while running the inner finally itself.
    if proc is not None:
        if 'owned_cleanup' not in result or proc.poll() is None:
            result['owned_cleanup']=cleanup_owned(proc)
        result.update(exit=proc.returncode,seconds=time.monotonic()-started,peak_group_rss_bytes=peak,
                      minimum_memory_free_percent=min_memory,minimum_disk_free_bytes=min_disk,
                      log_sha256=sha(log) if log.exists() else None)
        if not result['owned_cleanup']['leader_reaped'] or result['owned_cleanup']['errors']:
            result.update(status='failed',reason='owned process cleanup failed',fresh_credit=0)
write();print(json.dumps({k:result.get(k) for k in ['module','status','command_started','seconds','peak_group_rss_bytes','axiom_audits','reason']}),flush=True)
sys.exit(0 if result['status']=='passed' else 1)
