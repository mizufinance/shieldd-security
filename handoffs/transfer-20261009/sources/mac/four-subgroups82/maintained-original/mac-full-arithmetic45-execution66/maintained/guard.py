"""Distinct Join15 batch. No launch without exact external per-module admission.

This file does not resume an old controller or certify a runtime. Each call
launches at most one fixed module and stops on any incomplete/failed intent.
SIGKILL and detached processes missed between samples are not OS guarantees.
"""
import argparse, fcntl, hashlib, json, os, pathlib, re, signal, subprocess, sys, time

SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ilean', '.ir')
TERMS = {signal.SIGTERM, signal.SIGHUP, signal.SIGINT}
CANCELLED = False

def require(condition, reason):
    if not condition:
        raise RuntimeError(reason)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def strict_json(data):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, 'duplicate JSON key')
            result[key] = value
        return result
    return json.loads(data, object_pairs_hook=pairs)

def read_pin(pin):
    path = pathlib.Path(pin['path'])
    require(not path.is_symlink() and path.is_file(), 'pinned file missing/symlink: '+str(path))
    data = path.read_bytes()
    require(len(data) == pin['bytes'] and sha(data) == pin['sha256'], 'file identity: '+str(path))
    return data

# Deduplicate ignored identity verification only within a fixed_check phase.
# Stat identity includes ctime/mtime/inode; every pre/post fixed_check clears it.
# Callers needing bytes still use read_pin directly. No stored object contents.
_CHECKED = {}
def checked_pin(identity):
    path=pathlib.Path(identity['path'])
    require(not path.is_symlink() and path.is_file(), 'checked ordinary pinned file')
    stat=path.stat()
    signature=(stat.st_dev,stat.st_ino,stat.st_mode,stat.st_size,stat.st_mtime_ns,stat.st_ctime_ns,identity['bytes'],identity['sha256'])
    if _CHECKED.get(str(path))!=signature:
        read_pin(identity)
        after=path.stat()
        require((after.st_dev,after.st_ino,after.st_mode,after.st_size,after.st_mtime_ns,after.st_ctime_ns)==signature[:6], 'identity changed during hash')
        _CHECKED[str(path)]=signature

def read_bound(path, digest, maximum=16*1024*1024):
    p = pathlib.Path(path)
    require(p.is_file() and not p.is_symlink() and p.stat().st_size <= maximum, 'bound file')
    data = p.read_bytes()
    require(sha(data) == digest, 'bound SHA')
    return strict_json(data)

def pin(path):
    p = pathlib.Path(path)
    require(p.is_file() and not p.is_symlink(), 'pin ordinary file')
    data = p.read_bytes()
    return {'path':str(p), 'bytes':len(data), 'sha256':sha(data)}

def create(path, value):
    """Exclusive durable record; a write failure is retained, never overwritten."""
    data = (json.dumps(value, sort_keys=True, separators=(',',':'))+'\n').encode()
    p = pathlib.Path(path)
    fd = os.open(p, os.O_WRONLY|os.O_CREAT|os.O_EXCL, 0o600)
    try:
        with os.fdopen(fd, 'wb') as stream:
            stream.write(data); stream.flush(); os.fsync(stream.fileno())
        directory = os.open(p.parent, os.O_RDONLY)
        try: os.fsync(directory)
        finally: os.close(directory)
    except BaseException:
        # A partial exclusive file is a fail-closed consumed slot.
        raise

def strip_comments(source):
    result=[]; i=0; depth=0
    while i < len(source):
        if depth:
            if source.startswith('/-',i): depth+=1; i+=2
            elif source.startswith('-/',i): depth-=1; i+=2
            else: result.append('\n' if source[i]=='\n' else ' '); i+=1
        elif source.startswith('/-',i): depth=1; i+=2
        elif source.startswith('--',i):
            end=source.find('\n',i); i=len(source) if end<0 else end
        else: result.append(source[i]); i+=1
    require(depth==0, 'unclosed comment')
    return ''.join(result)

def uncached_direct_imports(data):
    clean=strip_comments(data.decode('utf-8'))
    names=[]
    for match in re.finditer(r'(?m)^\s*(?:(?:public|private)\s+)?(?:meta\s+)?import\s+([^\n]+)',clean):
        tokens=match.group(1).split()
        if tokens and tokens[0]=='all': tokens=tokens[1:]
        require(tokens and all(re.fullmatch(r'[A-Za-z0-9_.]+',x) for x in tokens), 'complete import syntax')
        names.extend(tokens)
    if not re.search(r'(?m)^\s*prelude\s*$',clean):names.insert(0,'Init')
    return names

# Pure parsing memoization by exact byte digest within this single guard process.
# Every source is still read and SHA checked at every fixed_check phase.
_IMPORT_HEADERS={}
def direct_imports(data):
    digest=sha(data)
    if digest not in _IMPORT_HEADERS:
        _IMPORT_HEADERS[digest]=tuple(uncached_direct_imports(data))
    return list(_IMPORT_HEADERS[digest])

def official_header(data):
    names=[];depth=0;prelude=False
    for raw in data.decode('utf-8').splitlines():
        out=[];i=0
        while i<len(raw):
            if depth:
                if raw.startswith('/-',i):depth+=1;i+=2
                elif raw.startswith('-/',i):depth-=1;i+=2
                else:i+=1
            elif raw.startswith('/-',i):depth=1;i+=2
            elif raw.startswith('--',i):break
            else:out.append(raw[i]);i+=1
        line=''.join(out).strip()
        if not line or line=='module':continue
        if line=='prelude':prelude=True;continue
        m=re.fullmatch(r'(?:(?:public|private)\s+)?(?:meta\s+)?import\s+(.+)',line)
        if m is None:break
        tokens=m[1].split();tokens=tokens[1:] if tokens[0]=='all' else tokens
        require(tokens and all(re.fullmatch(r'[A-Za-z0-9_.]+',x) for x in tokens),'official header syntax')
        names.extend(tokens)
    if not prelude:names.insert(0,'Init')
    return names

def source_check(data, spec):
    source=strip_comments(data.decode('utf-8'))
    require(len(data)<=262144, 'source cap')
    require('"' not in source and '`' not in source, 'source string/quotation refusal')
    forbidden=r'\b(?:sorry|admit|axiom|unsafe|implemented_by|extern|native_decide|run_tac|elab|initialize|macro|IO|ofReduceBool|skipKernelTC)\b|decide\s*\+native|#(?:eval|reduce|run|compile)|\bimport\s+all\b'
    require(not re.search(forbidden,source), 'forbidden source feature')
    options=re.findall(r'(?m)^\s*set_option\s+(\S+)\s+([^\n]+)',source)
    allowed={'autoImplicit':'false','maxHeartbeats':'900000','maxRecDepth':'8192','pp.all':'true in','linter.dupNamespace':'false'}
    require(all(key in allowed and val.strip()==allowed[key] for key,val in options), 'finite option whitelist')
    require(sum(key=='maxHeartbeats' for key,_ in options)==1 and sum(key=='maxRecDepth' for key,_ in options)==1, 'finite option count')
    imports=re.findall(r'(?m)^import ([A-Za-z0-9_.]+)\s*$',source)
    require(imports==spec['imports'], 'exact declared imports')
    checks=re.findall(r'(?m)^#check @([A-Za-z0-9_.]+)\s*$',source)
    axioms=re.findall(r'(?m)^#print axioms ([A-Za-z0-9_.]+)\s*$',source)
    require(checks==spec['audits'] and axioms==checks, 'exact named audits')
    commands=re.findall(r'(?m)^\s*(#[A-Za-z_]+)',source)
    require(set(commands)<= {'#check','#print'}, 'source command whitelist')

def audit_log(data, names):
    text=data.decode('utf-8'); remaining=text; records=[]
    require(not re.search(r'(?m)^(?:/[^\n]*:[0-9]+:[0-9]+: *| *)(?:warning|info|trace|error|panic)\s*:|sorryAx|uncaught exception|internal exception',text,re.I), 'diagnostic refusal')
    for name in names:
        pattern=r'^@?'+re.escape(name)+r'\s*:[\s\S]*?^\''+re.escape(name)+r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\s*$"
        matches=list(re.finditer(pattern,remaining,re.M))
        require(len(matches)==1, 'unique full-signature/axiom pair: '+name)
        m=matches[0]; axioms=[] if m.group(1) is None else [x.strip() for x in m.group(1).split(',') if x.strip()]
        require(set(axioms)<= {'propext','Quot.sound','Classical.choice'}, 'nonstandard axiom')
        full=m.group(0).split("\n'"+name+"'",1)[0].strip()
        records.append({'name':name,'full_type':full,'full_type_sha256':sha(full.encode()),'axioms':axioms})
        remaining=remaining[:m.start()]+remaining[m.end():]
    require(not remaining.strip(), 'unexplained/duplicate stdout')
    return records

def carried_check(config):
    history=strict_json(read_pin(config['carried_failure']))
    require(history['consumed_attempts']==config['carried_attempts'] and
            history['consumed_lean_seconds']==config['carried_lean_seconds'], 'exact protected previous consumption')
    def verify_tree(h):
        for parent in h.get('parents',[]): verify_tree(strict_json(read_pin(parent)))
        actual={str(p) for root in h['roots'] for p in pathlib.Path(root).rglob('*')
                if p.is_file() or p.is_symlink()}
        require(actual==set(h['entries']), 'protected history closed file/link keyset')
        for identity in h['entries'].values():
            if 'symlink_target' in identity:
                p=pathlib.Path(identity['path'])
                require(p.is_symlink() and os.readlink(p)==identity['symlink_target'], 'protected historical symlink')
                checked_pin(identity['target'])
            else: checked_pin(identity)
    verify_tree(history)
    receipts=[strict_json(read_pin(p)) for p in history['receipts']]
    require([r['status'] for r in receipts]==history['expected_statuses'], 'only exact protected failures; no new failure exception')
    require(len(receipts)==config['carried_attempts'] and sum(r['lean_seconds'] for r in receipts)==config['carried_lean_seconds'], 'complete previous attempt/time carry')
    require(all(r['cleanup']['clean'] is True and r['cleanup']['leader_reaped'] is True for r in receipts), 'previous cleanup uncertainty')
    for r in receipts:
        if r['status']=='passed':
            require(type(r['exit']) is int and r['exit']==0 and r['error'] is None,'previous pass exit')
            require(audit_log(read_pin(r['stdout']),[a['name'] for a in r['audits']])==r['audits'], 'previous exact type/axiom audits')
            for identity in r['objects'].values():checked_pin(identity)
        else: require(r['fresh_execution_credit']==0,'failed run zero proof credit')


def overlay_map(config):
    layout=strict_json(read_pin(config['overlay_manifest']))
    closure=strict_json(read_pin(config['closure']))
    closure['modules'].update(config['qualified_batch_imports'])
    expected={}
    for name,m in closure['modules'].items():
        require(name not in config['order'], 'inherited/new namespace collision')
        for suffix,identity in m['current_slots'].items():
            require(suffix in SUFFIXES, 'inherited companion suffix')
            if identity is not None:
                expected[str(pathlib.Path(config['own_cache'])/'ShielddSecurity'/(name+suffix))]=identity
    require(layout['aliases']==expected and layout['closure']==config['closure'], 'exact qualified overlay map')
    return expected


def first_package_file(roots, name, virtual_cache=None):
    # Lean 4.30 Util/Path.lean findWithExt chooses a PACKAGE root once.
    # It never falls back to another root when a module there is absent.
    package=name.split('.')[0]; relative=name.replace('.','/')+'.olean'
    for root in roots:
        p=pathlib.Path(root)
        if (p/package).is_dir() or (p/(package+'.olean')).exists() or (
                virtual_cache is not None and str(p)==virtual_cache and package=='ShielddSecurity'):
            return str(p/relative)
    return None


def own_keyset(config, records):
    cache=pathlib.Path(config['own_cache']); aliases=overlay_map(config)
    expected={}
    for rec in records:
        for path, identity in rec['objects'].items(): expected[path]=identity
    require(not (set(expected)&set(aliases)), 'own/inherited object collision')
    if not cache.exists():
        require(not expected, 'missing accepted own cache'); return
    require(cache.is_dir() and not cache.is_symlink(), 'ordinary overlay root')
    files=set(); directories={cache,cache/'ShielddSecurity'}
    for path in cache.rglob('*'):
        key=str(path)
        if path.is_symlink():
            require(key in aliases and os.readlink(path)==aliases[key]['path'], 'unapproved inherited symlink')
            checked_pin(aliases[key]);files.add(key)
        elif path.is_dir(): require(path in directories, 'unexpected own cache directory')
        else:
            require(key in expected and pin(path)==expected[key], 'exact built own companion identity')
            files.add(key)
    require(files==set(aliases)|set(expected), 'exact overlay keyset/companions')
    for name in config['order'][len(records):]:
        for suffix in SUFFIXES:
            p=cache/'ShielddSecurity'/(name+suffix)
            require(not p.exists() and not p.is_symlink(), 'future own object present')


def initialize_overlay(config):
    cache=pathlib.Path(config['own_cache']); aliases=overlay_map(config)
    if cache.exists():
        own_keyset(config,[]);return
    cache.mkdir(); (cache/'ShielddSecurity').mkdir()
    for path,identity in aliases.items():
        checked_pin(identity)
        os.symlink(identity['path'],path) # absolute exact checked input; no object copy
    directory=os.open(cache/'ShielddSecurity',os.O_RDONLY)
    try: os.fsync(directory)
    finally: os.close(directory)
    own_keyset(config,[])


def fixed_check(config, records):
    _CHECKED.clear()
    carried_check(config)
    for identity in config['static_records'].values(): read_pin(identity)
    for module_name,spec in config['modules'].items():
        checked_pin(spec['source']);root=pathlib.Path(spec['source_root']);source=pathlib.Path(spec['source']['path'])
        require(root.is_dir() and not root.is_symlink() and source==root/'ShielddSecurity'/(module_name+'.lean') and source.resolve()==source,'exact canonical per-module source root')
    spec=config['modules'][config['_active_module']]
    source_check(read_pin(spec['source']),spec)
    closure=strict_json(read_pin(config['closure']))
    require(not (set(closure['modules'])&set(config['qualified_batch_imports'])), 'qualified name collision')
    closure['modules'].update(config['qualified_batch_imports'])
    official=strict_json(read_pin(config['official']))
    require(official['manifest_count']<=4 and config['official']['bytes']<=16*1024*1024, 'official manifest cap')
    require(set(direct_imports(read_pin(spec['source']))) <= {'ShielddSecurity.'+n for n in closure['modules']} | {'ShielddSecurity.'+n for n in config['order'][:len(records)]} | set(official['official_modules']), 'complete fresh module custom/official imports')
    package_root=pathlib.Path(config['project'])/'.lake/packages'
    tool_root=pathlib.Path(config['lean']).resolve().parents[1]
    for relative,digest in official['manifest']['files'].items():
        if not relative.endswith('.lean'):continue
        path=tool_root/pathlib.Path(relative).relative_to('lean4') if relative.startswith('lean4/') else package_root/relative
        data=path.read_bytes();require(sha(data)==digest,'official source identity')
        header=official_header(data)
        require(set(header)<=set(official['official_modules']),'complete official source import closure')
    for path,identity in official['slots'].items():
        if identity is not None: checked_pin(identity)
        else: require(not pathlib.Path(path).exists() and not pathlib.Path(path).is_symlink(), 'official companion absence')
    for path, identity in closure['companion_slots'].items():
        if identity is None: require(not pathlib.Path(path).exists() and not pathlib.Path(path).is_symlink(), 'inherited companion absence')
        else: checked_pin(identity)
    aliases=overlay_map(config)
    virtual=config['own_cache'] if not pathlib.Path(config['own_cache']).exists() else None
    for name,m in closure['modules'].items():
        declared=direct_imports(read_pin(m['source']))
        require(all(x in {'ShielddSecurity.'+k for k in closure['modules']}|set(official['official_modules']) for x in declared), 'complete custom/official direct import coverage');require([x for x in declared if x.startswith('ShielddSecurity.')]==m['custom_imports'], 'transitive declared import identity')
        checked_pin(m['object'])
        receipt=strict_json(read_pin(m['receipt']))
        require(receipt['status']=='passed', 'inherited receipt not passed')
        for identity in m['current_slots'].values():
            if identity is not None: checked_pin(identity)
        selected=first_package_file(config['lean_path'],'ShielddSecurity.'+name,virtual)
        require(selected in aliases and aliases[selected]==m['object'], 'actual first custom PACKAGE root')
    for alias in config['alias_records']: read_pin(alias)
    for name in official['official_modules']:
        selected=first_package_file(config['lean_path'],name,virtual)
        identity=official['slots'].get(selected)
        require(identity is not None and identity['path']==selected, 'actual first official PACKAGE root')
        checked_pin(identity)
    own_keyset(config,records)

def processes():
    raw=subprocess.check_output(['/bin/ps','-axo','pid=,ppid=,pgid=,rss=,lstart=,comm='],timeout=5).decode()
    result={}
    for line in raw.splitlines():
        p=line.split(None,9)
        require(len(p)==10, 'ps format')
        result[int(p[0])]={'ppid':int(p[1]),'pgid':int(p[2]),'rss':int(p[3])*1024,'birth':' '.join(p[4:9]),'comm':p[9]}
    return result

def free_memory():
    raw=subprocess.check_output(['/usr/bin/memory_pressure','-Q'],timeout=10).decode()
    matches=re.findall(r'System-wide memory free percentage:\s*(\d+)%',raw)
    require(len(matches)==1, 'memory observation')
    return int(matches[0])

def bytes_in(root, aliases):
    root=pathlib.Path(root); total=metadata=0
    if root.exists():
        for path in root.rglob('*'):
            if path.is_symlink():
                require(str(path) in aliases and os.readlink(path)==aliases[str(path)]['path'], 'unapproved batch symlink')
                total+=path.lstat().st_size # link itself, never the immutable target
                continue
            if path.is_file():
                size=path.stat().st_size; total+=size
                if 'runtime' in path.relative_to(root).parts or path.suffix in {'.json','.jsonl','.log','.stdout','.stderr'}: metadata+=size
    return total,metadata

def bounds(config):
    def history_aliases(identity):
        h=strict_json(read_pin(identity)); result={}
        for parent in h.get('parents',[]): result.update(history_aliases(parent))
        result.update(h.get('historical_aliases',{}));return result
    aliases={**history_aliases(config['carried_failure']),**overlay_map(config)};total=metadata=0
    for root in config['charged_roots']:
        physical,md=bytes_in(root,aliases);total+=physical;metadata+=md
    require(total<=2*1024*1024*1024 and metadata<=768*1024*1024, 'batch disk/metadata cap')
    stat=os.statvfs(config['batch_root'])
    disk=stat.f_bavail*stat.f_frsize; memory=free_memory()
    require(disk>=2*1024*1024*1024 and memory>=15, 'RAM/disk admission')
    return {'free_memory_percent':memory,'free_disk_bytes':disk,'batch_bytes':total,'metadata_bytes':metadata}

def launch_reserve(observation):
    require(observation['metadata_bytes']<=764*1024*1024, 'reserve streams/receipt metadata')
    require(observation['batch_bytes']<=2032*1024*1024, 'reserve new object/streams/receipt')

def state(config):
    runtime=pathlib.Path(config['runtime']); ledger=runtime/'ledger.jsonl'
    if not runtime.exists(): return [],None
    require(ledger.is_file(), 'missing existing ledger')
    raw=ledger.read_bytes(); require(not raw or raw.endswith(b'\n'), 'incomplete ledger')
    events=[strict_json(line) for line in raw.splitlines()]
    require(len(events)%2==0, 'unfinished/failed launch intent; no retry')
    records=[]; claims=set(); receipts=set();logs=set()
    for i in range(0,len(events),2):
        intent,result=events[i:i+2]; require(intent['kind']=='intent' and result['kind']=='result', 'ledger ordering')
        require(result['intent_sha256']==sha((json.dumps(intent,sort_keys=True,separators=(',',':'))+'\n').encode()), 'intent/result linkage')
        receipt=strict_json(read_pin(result['receipt']))
        require(receipt['status']=='passed' and type(receipt['exit']) is int and receipt['exit']==0 and receipt['cleanup']['clean'] is True, 'prior nonpassed intent; no retry')
        require(receipt['module']==config['order'][len(records)], 'named topology')
        for path,identity in receipt['objects'].items(): read_pin(identity)
        read_pin(receipt['stdout']); read_pin(receipt['stderr']); read_pin(intent['claim'])
        claims.add(intent['claim']['path']);receipts.add(result['receipt']['path'])
        logs.update([receipt['stdout']['path'],receipt['stderr']['path']])
        records.append(receipt)
    for folder,expected in [('claims',claims),('receipts',receipts),('logs',logs)]:
        actual={str(p) for p in (runtime/folder).iterdir()}
        require(actual==expected, 'orphan/partial runtime record; no reset')
    genesis=strict_json((runtime/'genesis.json').read_bytes())
    require(genesis['config_sha256']==config['_config_sha256'] and genesis['inventory_sha256']==config['_inventory_sha256'], 'runtime genesis identity')
    require({p.name for p in runtime.iterdir()}=={'genesis.json','ledger.jsonl','claims','logs','receipts','tmp','lock'}, 'runtime closed keyset')
    require(not any((runtime/'tmp').iterdir()), 'unqualified retained Lean temp files')
    require(config['carried_attempts']+len(events)//2<=config['limits']['total_attempts'] and config['carried_lean_seconds']+sum(x['lean_seconds'] for x in records)<=config['limits']['aggregate_lean_seconds'], 'cumulative pacing including protected consumption')
    return records,sha(raw) if raw else None

def append_event(path,value):
    data=(json.dumps(value,sort_keys=True,separators=(',',':'))+'\n').encode()
    with open(path,'ab',buffering=0) as stream: stream.write(data);os.fsync(stream.fileno())

def cancellation(signum,frame):
    global CANCELLED
    CANCELLED=True

def cancelled(): require(not CANCELLED, 'cancellation requested')

def owned(table, proc, root_birth, seen):
    if proc.pid in table and table[proc.pid]['birth']==root_birth: seen[proc.pid]=root_birth
    changed=True
    while changed:
        changed=False
        for pid,p in table.items():
            if p['ppid'] in seen and pid not in seen:
                seen[pid]=p['birth'];changed=True
    return {pid:p for pid,p in table.items() if (pid in seen and seen[pid]==p['birth']) or p['pgid']==proc.pid}

def cleanup(proc,root_birth,seen):
    errors=[]; sampled=[]
    try:
        table=processes(); targets=owned(table,proc,root_birth,seen); sampled=sorted(targets)
        for sig in (signal.SIGTERM,signal.SIGKILL):
            for group in {p['pgid'] for p in targets.values()}|{proc.pid}:
                require(group!=os.getpgrp(), 'cleanup own runner group refusal')
                try: os.killpg(group,sig)
                except ProcessLookupError: pass
            if proc.poll() is None:
                try: proc.wait(timeout=2)
                except subprocess.TimeoutExpired: pass
            table=processes();targets=owned(table,proc,root_birth,seen)
            if not targets: break
        if proc.poll() is None: proc.wait(timeout=2)
        require(not targets and proc.poll() is not None, 'owned cleanup uncertainty')
    except BaseException as error: errors.append(repr(error))
    return {'clean':not errors,'errors':errors,'observed_owned_pids':sampled,'leader_reaped':proc.poll() is not None,'scope':'birth-qualified sampled descendants/groups; no unsampled-daemon/SIGKILL guarantee'}

def execute(args):
    require(sys.flags.isolated==1 and sys.flags.dont_write_bytecode==1 and sys.flags.no_site==1 and sys.flags.optimize==0, 'python -I -B -S, no -O')
    require(not (signal.pthread_sigmask(signal.SIG_BLOCK,set()) & TERMS), 'parent catchable signals must start unblocked')
    config=read_bound(args.config,args.config_sha256)
    inventory=read_bound(args.inventory,args.inventory_sha256)
    require(set(inventory)=={'guard.py','prepare.py'} and inventory['guard.py']==pin(__file__), 'executing guard inventory')
    for identity in inventory.values(): read_pin(identity)
    require({p.name for p in pathlib.Path(__file__).parent.iterdir()}==set(inventory), 'closed maintained keyset')
    require(pathlib.Path(__file__).parent==pathlib.Path(config['maintained']), 'fixed guard path')
    config['_config_sha256']=args.config_sha256;config['_inventory_sha256']=args.inventory_sha256
    require(pathlib.Path(sys.executable).resolve()==pathlib.Path(config['python']).resolve(), 'resolved Python binary')
    require(config['lean_environment']['LEAN_NUM_THREADS']=='1' and config['lean_environment']['LEAN_PATH']==':'.join(config['lean_path']), 'explicit Lean environment')
    admission=read_bound(args.admission,args.admission_sha256,65536)
    require(admission['approved'] is True and admission['config_sha256']==args.config_sha256 and admission['inventory_sha256']==args.inventory_sha256, 'external reviewed admission')
    name=args.module; require(name in config['order'] and admission['module']==name, 'exact name admission')
    config['_active_module']=name
    require(config['canonical_context']=='cec1b30defc23497c8e9b30528dca12b09d328ea' and config['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a', 'source/runtime context')
    records,digest=state(config)
    require(admission['prior_ledger_sha256']==digest and admission['prior_passed']==len(records), 'complete externally anchored prior state')
    require(name==config['order'][len(records)] and len(records)+config['carried_attempts']<config['limits']['total_attempts'], 'next named module and remaining attempts')
    require(admission['carried_failure_sha256']==config['carried_failure']['sha256'], 'externally anchored known failure')
    cancelled();pre=bounds(config);launch_reserve(pre)
    require(not any(pathlib.Path(p['comm']).name in {'lean','lake','cargo','rustc'} for p in processes().values()), 'one heavy physical-host lane')
    runtime=pathlib.Path(config['runtime'])
    if not runtime.exists():
        runtime.mkdir(); (runtime/'claims').mkdir();(runtime/'logs').mkdir();(runtime/'receipts').mkdir();(runtime/'tmp').mkdir()
        create(runtime/'genesis.json',{'config_sha256':args.config_sha256,'inventory_sha256':args.inventory_sha256,'external_admission_sha256':args.admission_sha256})
        (runtime/'ledger.jsonl').touch(exist_ok=False)
    lockfd=os.open(runtime/'lock',os.O_CREAT|os.O_RDWR,0o600)
    locked=False;proc=None;seen={};root_birth='';cleanup_result=None;receipt=None;intent=None
    try:
        fcntl.flock(lockfd,fcntl.LOCK_EX|fcntl.LOCK_NB);locked=True
        records,digest=state(config)
        require(admission['prior_ledger_sha256']==digest and admission['prior_passed']==len(records), 'under-lock state')
        cancelled();pre=bounds(config);launch_reserve(pre)
        require(not any(pathlib.Path(p['comm']).name in {'lean','lake','cargo','rustc'} for p in processes().values()), 'under-lock host lane')
        cache=pathlib.Path(config['own_cache'])
        if not cache.exists(): initialize_overlay(config)
        fixed_check(config,records) # actual PACKAGE lookup after layout exists, under held lock
        cancelled();pre=bounds(config);launch_reserve(pre)
        require(not any(pathlib.Path(p['comm']).name in {'lean','lake','cargo','rustc'} for p in processes().values()), 'immediate host lane')
        number=len(records)+config['carried_attempts']+1; spec=config['modules'][name]
        stdout=runtime/'logs'/f'{number:02d}-{name}.stdout';stderr=runtime/'logs'/f'{number:02d}-{name}.stderr'
        out=cache/'ShielddSecurity'/(name+'.olean')
        command=[config['lean'],'-j1','-M2048','-R',spec['source_root'],'-o',str(out),spec['source']['path']]
        receipt_path=runtime/'receipts'/f'{number:02d}-{name}.json'
        oldmask=signal.pthread_sigmask(signal.SIG_BLOCK,TERMS)
        started=time.monotonic();peak=0;failure=None;observations=[];audits=[];objects={}
        try:
            cancelled();claim=runtime/'claims'/(args.admission_sha256+'.json')
            create(claim,{'admission_sha256':args.admission_sha256,'module':name,'ordinal':number})
            intent={'kind':'intent','ordinal':number,'module':name,'claim':pin(claim),'admission_sha256':args.admission_sha256,'command':command,'source':spec['source']}
            append_event(runtime/'ledger.jsonl',intent)
            with open(stdout,'xb') as so,open(stderr,'xb') as se:
                def unmask(): signal.pthread_sigmask(signal.SIG_SETMASK,oldmask)
                proc=subprocess.Popen(command,cwd=config['project'],env=config['lean_environment'],stdin=subprocess.DEVNULL,stdout=so,stderr=se,start_new_session=True,preexec_fn=unmask)
                table=processes();require(proc.pid in table,'leader vanished before birth qualification');root_birth=table[proc.pid]['birth'];seen[proc.pid]=root_birth
                signal.pthread_sigmask(signal.SIG_SETMASK,oldmask)
                consumed=config['carried_lean_seconds']+sum(r['lean_seconds'] for r in records); last_resource=0
                while proc.poll() is None:
                    cancelled();elapsed=time.monotonic()-started
                    require(elapsed<=240 and consumed+elapsed<=config['limits']['aggregate_lean_seconds'], 'module/aggregate seconds')
                    table=processes();members=owned(table,proc,root_birth,seen)
                    rss=sum(p['rss'] for p in members.values());peak=max(peak,rss)
                    require(rss<=4*1024*1024*1024, 'owned group RSS')
                    require(stdout.stat().st_size<=2*1024*1024 and stderr.stat().st_size<=2*1024*1024, 'stream bytes')
                    if elapsed-last_resource>=1:
                        observation=bounds(config);observations.append({'seconds':elapsed,'rss':rss,**observation});last_resource=elapsed
                    time.sleep(.2)
        except BaseException as error: failure=repr(error)
        finally:
            signal.pthread_sigmask(signal.SIG_BLOCK,TERMS)
            if proc is not None: cleanup_result=cleanup(proc,root_birth,seen)
            else: cleanup_result={'clean':True,'errors':[],'leader_reaped':True,'scope':'no owned process assigned; intent remains consumed'}
        elapsed=time.monotonic()-started
        exitcode=None if proc is None else proc.returncode
        try:
            require(failure is None and type(exitcode) is int and exitcode==0 and cleanup_result['clean'] and not CANCELLED, 'process/failure/cleanup refusal')
            require(elapsed<=240 and config['carried_lean_seconds']+sum(r['lean_seconds'] for r in records)+elapsed<=config['limits']['aggregate_lean_seconds'], 'post-run aggregate seconds including retained failure')
            require(stdout.stat().st_size<=2*1024*1024 and stderr.stat().st_size<=2*1024*1024, 'post-run stream bytes')
            require(stderr.read_bytes()==b'', 'nonempty stderr')
            audits=audit_log(stdout.read_bytes(),spec['audits'])
            for suffix in SUFFIXES:
                p=cache/'ShielddSecurity'/(name+suffix)
                if p.exists(): objects[str(p)]=pin(p)
            require(str(out) in objects, 'missing own olean')
            require(sum(p['bytes'] for p in objects.values())<=8*1024*1024, 'per-module aggregate own objects')
            provisional={'objects':objects}
            fixed_check(config,records+[provisional]);post=bounds(config)
        except BaseException as error:
            if failure is None: failure=repr(error)
            post=None
        receipt={'module':name,'status':'passed' if failure is None else 'failed','exit':exitcode,'error':failure,'command':command,'source':spec['source'],'objects':objects,'audits':audits,'stdout':pin(stdout) if stdout.exists() else None,'stderr':pin(stderr) if stderr.exists() else None,'lean_seconds':elapsed,'peak_group_rss':peak,'cleanup':cleanup_result,'preflight':pre,'postflight':post,'observations':observations,'inherited_closure':config['closure'],'official_manifest':config['official'],'carried_failure':config['carried_failure'],'all_attempts':number,'all_lean_seconds':config['carried_lean_seconds']+sum(r['lean_seconds'] for r in records)+elapsed,'fresh_execution_credit':1 if failure is None else 0}
        if len(json.dumps(receipt).encode())>1024*1024:
            failure='receipt size refusal';receipt.update(status='failed',error=failure,audits=[],fresh_execution_credit=0)
        create(receipt_path,receipt)
        append_event(runtime/'ledger.jsonl',{'kind':'result','intent_sha256':sha((json.dumps(intent,sort_keys=True,separators=(',',':'))+'\n').encode()),'receipt':pin(receipt_path)})
        bounds(config)
        require(failure is None, 'failed intent retained; STOP')
        print(json.dumps({'status':'passed','receipt':pin(receipt_path),'ledger':pin(runtime/'ledger.jsonl')}))
    finally:
        # Monitoring exceptions must not orphan the owned process. Cached cleanup
        # is never rerun; a failed cleanup is a fatal retained uncertainty.
        signal.pthread_sigmask(signal.SIG_BLOCK,TERMS)
        if proc is not None and cleanup_result is None: cleanup_result=cleanup(proc,root_birth,seen)
        if locked: fcntl.flock(lockfd,fcntl.LOCK_UN)
        os.close(lockfd)
        signal.pthread_sigmask(signal.SIG_SETMASK,oldmask if 'oldmask' in locals() else set())

def main():
    parser=argparse.ArgumentParser()
    for option in ('config','config-sha256','inventory','inventory-sha256','admission','admission-sha256','module'): parser.add_argument('--'+option,required=True)
    args=parser.parse_args()
    for sig in TERMS: signal.signal(sig,cancellation)
    execute(args)

if __name__=='__main__': main()
