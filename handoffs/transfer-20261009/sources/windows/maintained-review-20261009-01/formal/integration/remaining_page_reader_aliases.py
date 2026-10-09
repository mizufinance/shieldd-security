"""Exact-byte adapter for the frozen remaining-writer/page-reader filename gap.

The native qualifier remains authoritative. Original manifest/page bytes and
FALSE flags are preserved; fresh reader aliases carry no qualification claim.
Rows are hardlinked without a second compilation or source rewrite, then the
same private native qualifier reads/computes/compares all four complete spools.
"""
from pathlib import Path
import hashlib,json,os,sys

SCOPES={'sender':19,'receiver':19,'volume':32,'encryption':25,'audit-sender':2,
        'audit-receiver':2,'routing':7,'statement':14}
BINARY='/root/.cache/shieldd-security-verification/transfer-epk-balance-blinding-binary-20261004-03/transfer-ownership-inspection'

def read(path,limit):
    path=Path(path)
    if not path.is_file() or path.is_symlink():raise ValueError('regular original captured file required')
    with path.open('rb') as handle:data=handle.read(limit+1)
    if not data or len(data)>limit:raise ValueError('bounded original remaining metadata required')
    return data

def alias(first,repeat,destination,scope):
    if scope not in SCOPES:raise ValueError('exact existing remaining scope required')
    first,repeat,destination=map(Path,(first,repeat,destination))
    if destination.exists():raise ValueError('fresh reader-alias directory required')
    manifests=[read(str(prefix)+'.pending.json',32768) for prefix in (first,repeat)]
    if manifests[0]!=manifests[1]:raise ValueError('actual first/repeat pending manifest differs')
    manifest=json.loads(manifests[0])
    if (manifest.get('schema')!='shieldd-transfer-remaining-source-pages-v1' or manifest.get('scope')!=scope
            or manifest.get('ordinary_full_ordered_rows_equal') is not False
            or manifest.get('repeated_observations_equal') is not False or manifest.get('qualification') is not False
            or len(manifest.get('pages',[]))!=SCOPES[scope]):raise ValueError('actual pending remaining family required')
    pages=[]
    for ordinal,descriptor in enumerate(manifest['pages']):
        suffix=f'pending-page-{ordinal:03d}.json'
        if descriptor.get('ordinal')!=ordinal or descriptor.get('suffix')!=suffix:
            raise ValueError('exact captured remaining filename descriptor required')
        raw=[read(str(prefix)+'.'+suffix,4194304) for prefix in (first,repeat)]
        # The unchanged descriptor's BLAKE3 is checked by the native qualifier.
        # This filename adapter establishes byte identity, not semantic acceptance.
        if (raw[0]!=raw[1] or descriptor.get('bytes')!=len(raw[0]) or
                not isinstance(descriptor.get('blake3'),str) or len(descriptor['blake3'])!=64 or
                any(ch not in '0123456789abcdef' for ch in descriptor['blake3'])):
            raise ValueError('actual original first/repeat page bytes required')
        pages.append((suffix,raw[0]))
    # No output before all bounded original pages/descriptors are accepted.
    destination.mkdir();pins={};links=[];prefixes=[]
    def retained(source,target,raw=None):
        if raw is None:raw=read(source,32768)
        target.write_bytes(raw)
        digest=hashlib.sha256(raw).hexdigest();pins[str(source)]=digest;pins[str(target)]=digest
    for tag,prefix,manifest_bytes in zip(('first','repeat'),(first,repeat),manifests):
        folder=destination/tag;folder.mkdir();target=folder/'capture';prefixes.append(str(target))
        retained(str(prefix)+'.pending.json',Path(str(target)+'.pending.json'),manifest_bytes)
        retained(str(prefix)+'.shape.json',Path(str(target)+'.shape.json'))
        source=Path(str(prefix)+'.rows');row_target=Path(str(target)+'.rows')
        if not source.is_file() or source.is_symlink():raise ValueError('original native row spool required')
        os.link(source,row_target)
        if not os.path.samefile(source,row_target):raise ValueError('same exact native row spool required')
        stat=source.stat();links.append(dict(source=str(source),target=str(row_target),
            size=stat.st_size,mtime_ns=stat.st_mtime_ns,device=stat.st_dev,inode=stat.st_ino))
        for ordinal,(suffix,raw) in enumerate(pages):
            retained(str(prefix)+'.'+suffix,Path(str(target)+f'.page{ordinal}.pending.json'),raw)
    receipt=dict(scope=scope,pins=pins,rows=links,prefixes=prefixes,qualification=False,
        schema='shieldd-remaining-exact-reader-alias-v1',
        semantic_scope='Reader filename adaptation only; native full four-spool qualification must run; original pending bytes/flags unchanged')
    (destination/'receipt.json').write_text(json.dumps(receipt,indent=2))
    return prefixes

def audit(destination):
    receipt=json.loads(read(Path(destination)/'receipt.json',1048576))
    for name,digest in receipt['pins'].items():
        if hashlib.sha256(read(name,4194304)).hexdigest()!=digest:raise ValueError('original/alias metadata bytes changed')
    for pair in receipt['rows']:
        source,target=Path(pair['source']),Path(pair['target']);stat=source.stat()
        if not os.path.samefile(source,target) or any(getattr(stat,key)!=pair[name]
            for key,name in [('st_size','size'),('st_mtime_ns','mtime_ns'),('st_dev','device'),('st_ino','inode')]):
            raise ValueError('native original/alias spool identity changed')

if __name__=='__main__':
    if sys.argv[1]=='audit':audit(sys.argv[2])
    else:
        _,scope,first,repeat,destination,ordinary1,ordinary2=sys.argv
        prefixes=alias(first,repeat,destination,scope)
        audit(destination)
        os.execv(BINARY,[BINARY,'qualify-spools',prefixes[0],ordinary1,ordinary2,prefixes[1]])
