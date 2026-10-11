"""Review exact parser memoization and iterative provenance traversal; no verifier launch."""
from pathlib import Path
import ast,difflib,hashlib,json,re,importlib.util
J=Path(__file__).parent;W=J.parent
def sha(b):return hashlib.sha256(b).hexdigest()
baseline=W/'mac-full-arithmetic45-execution195/maintained/guard.py'
assert sha(baseline.read_bytes())=='c4ad8921031707767f33c5445f0eb772a844e8690c511361104db31c0b04ef40'
new=W/'mac-full-arithmetic45-execution198/maintained/guard.py'
assert sha(new.read_bytes())=='0bd4749151b31367d41607e5960982c4258860c9fe1d2f51dbcc6d5dfc5e5f4b'
old=baseline.read_text();expected=old.replace('def audit_log(data, names):','def _parse_audit_log(data, names):')
before="    require(not remaining.strip(), 'unexplained/duplicate stdout')\n    return records"
after="""    require(not remaining.strip(), 'unexplained/duplicate stdout')
    return records

_AUDIT_CACHE={}
_AUDIT_CACHE_BYTES=0
def audit_log(data,names):
    global _AUDIT_CACHE_BYTES
    key=(sha(data),tuple(names))
    if key in _AUDIT_CACHE:
        return strict_json(_AUDIT_CACHE[key])
    records=_parse_audit_log(data,names)
    encoded=json.dumps(records,sort_keys=True,separators=(',',':')).encode()
    charge=len(encoded)+512+sum(len(n) for n in names)
    if len(_AUDIT_CACHE)<2048 and _AUDIT_CACHE_BYTES+charge<=32*1024*1024:
        _AUDIT_CACHE[key]=encoded
        _AUDIT_CACHE_BYTES+=charge
    return records"""
assert expected.count(before)==1;expected=expected.replace(before,after)
assert expected==new.read_text()
later=W/'mac-full-arithmetic45-execution199/maintained/guard.py'
assert sha(later.read_bytes())=='df0817bc2c071171583d69a304bb25e108ae6f8e42048dbd2e135996f6bc606f'
expected=new.read_text();before="        for parent in h.get('parents',[]): verify_tree(strict_json(read_pin(parent)))\n"
assert expected.count(before)==1;expected=expected.replace(before,'')
before='    verify_tree(history)\n';after="""    pending=[config['carried_failure']]
    while pending:
        h=strict_json(read_pin(pending.pop()))
        verify_tree(h)
        pending.extend(h.get('parents',[]))
"""
assert expected.count(before)==1;expected=expected.replace(before,after)
assert expected==later.read_text()
# Execute only pure report parsers from the immutable source, with no launch API.
tree=ast.parse(new.read_text());names={'require','sha','strict_json','_parse_audit_log','audit_log'}
pure=[x for x in tree.body if isinstance(x,ast.FunctionDef)and x.name in names]
assert len(pure)==5
env=dict(hashlib=hashlib,json=json,re=re,_AUDIT_CACHE={},_AUDIT_CACHE_BYTES=0)
exec(compile(ast.Module(body=pure,type_ignores=[]),str(new),'exec'),env)
module=json.loads((W/'mac-prior-global170-kernel-result01/qualified-modules01.json').read_bytes())[0]
receipt=json.loads(Path(module['receipt']['path']).read_bytes());data=Path(receipt['stdout']['path']).read_bytes();decls=[x['name']for x in receipt['audits']]
assert env['audit_log'](data,decls)==env['_parse_audit_log'](data,decls)==receipt['audits']
hit=env['audit_log'](data,decls);hit[0]['name']='modified returned copy'
assert env['audit_log'](data,decls)==receipt['audits']
reordered=list(reversed(decls));assert env['audit_log'](data,reordered)==env['_parse_audit_log'](data,reordered)
assert len(env['_AUDIT_CACHE'])==2
for body,order in [(data+b'\nwarning: injected warning\n',decls),(data,decls+['ShielddSecurity.NonexistentAudit'])]:
 try:env['audit_log'](body,order)
 except RuntimeError:pass
 else:raise AssertionError('Changed diagnostic/missing declaration unexpectedly accepted')
env['_AUDIT_CACHE']={};env['_AUDIT_CACHE_BYTES']=32*1024*1024
assert env['audit_log'](data,decls)==receipt['audits']and not env['_AUDIT_CACHE']
spec=importlib.util.spec_from_file_location('preserved',J/'read_preserved_mac_config06.py');reader=importlib.util.module_from_spec(spec);spec.loader.exec_module(reader)
physical={'threads':1,'heap_MiB':2048,'group_rss_bytes':4294967296,'module_seconds':240,'minimum_free_RAM_percent':15,'minimum_free_disk_bytes':2147483648,'heartbeats':900000,'recdepth':8192}
records=[]
for stage,path,prior in [(198,new,baseline),(199,later,new)]:
 config=json.loads(reader.read_config(path.parent.parent/'config01.json'))
 assert all(config['limits'][k]==v for k,v in physical.items())and config['lean_environment']['LEAN_NUM_THREADS']=='1'
 (J/f'pending-mac-metadata-cache-guard-delta{stage}.diff').write_text(''.join(difflib.unified_diff(prior.read_text().splitlines(True),path.read_text().splitlines(True),fromfile=str(prior),tofile=str(path))))
 records.append(dict(path=str(path),bytes=path.stat().st_size,sha256=sha(path.read_bytes())))
out=dict(status='PASSED',kind='Exact metadata-only source delta review plus pure parser tests; no Lean/native launch',guards=records,physical_limits=physical,audit_cache='Original parser unchanged; memo keyed by exact stdout SHA and ordered names, returns independent strict-JSON record copies; 2048 entries/32MiB bound; injected diagnostics/missing declarations rejected; changed name order revalidated in separate cache entry',history_traversal='Same exact pinned root and every parent traversed with explicit stack; closed-keyset/content/symlink/receipt checks remain intact. Iteration removes Python recursion depth failure without altering Lean limits or physical protections.',full_transfer='OPEN')
(J/'mac-metadata-cache-guard-review06.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(status='PASSED',guards=len(records),pure_parser_tests='PASSED',physical_guards_unchanged=True)))
