"""Lossless transport of existing inventory/provenance; no proof execution."""
from pathlib import Path
import hashlib,io,json,tarfile
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent;MAIN=DIAG.parent.parent
def pin(p):
    p=Path(p);b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
floor=DIAG/'transfer-external-floor-complete-20261010-08/external-floor.json'
assert pin(floor)['bytes']==12241910 and pin(floor)['sha256']=='82ef07658ca7d127e3e58c293946c87dfdb66dba4a94ad2683c9c7158e92ba72'
data=json.loads(floor.read_bytes());assert data['admission_ready'] and not data['gaps']
assert len(data['modules'])==3612 and len(data['immutable_files'])==20202
assert not any(module.startswith('ShielddSecurity') for module in data['modules'])
sources={}
def add(p,name):
    p=Path(p);assert p.is_file() and p.stat().st_size<16*1024**2
    assert name not in sources;sources[name]=p
for folder,names in [
 ('transfer-external-floor-complete-20261010-08',['external-floor.json','prepare.py']),
 ('transfer-external-floor-complete-20261010-06',['external-floor.json','prepare.py','inventory.py','cache-qualification.json']),
 ('transfer-external-package-overlay-20261010-03',['composition-review.json','prepare.py','prepare_successor.py']),
 ('transfer-cache-qualified78-20261010-01',['qualification.json','assemble.py']),
 ('transfer-cache-lucas-extract-20261010-01',['plan.json','prepare.py','execute_metadata.py','result.json','stdout.txt'])]:
    for name in names:add(DIAG/folder/name,'original/'+folder+'/'+name)
for key in ['official_reference','additional_official_reference','lucas_field_official_reference','first_package_composition']:
    row=data[key];assert pin(row['path'])==row
    if Path(row['path']) not in sources.values():add(row['path'],'official-references/'+key+'.json')
seen=set()
def provenance(value):
    if isinstance(value,dict):
        if all(k in value for k in ['path','bytes','sha256']):
            p=Path(value['path'])
            if p.is_relative_to(DIAG) and p.suffix in ['.json','.py','.txt'] and p.is_file() and p.stat().st_size<1048576:
                assert pin(p)=={k:value[k] for k in ['path','bytes','sha256']}
                if p not in sources.values():add(p,'original/'+p.relative_to(DIAG).as_posix())
                if p.suffix=='.json' and str(p) not in seen:
                    seen.add(str(p));provenance(json.loads(p.read_bytes()))
        for key,child in value.items():
            if key not in ['files','records','objects','immutable_files','modules']:provenance(child)
    elif isinstance(value,list):
        for child in value:provenance(child)
for name in ['transfer-cache-qualified78-20261010-01/qualification.json','transfer-external-floor-complete-20261010-06/cache-qualification.json']:
    provenance(json.loads((DIAG/name).read_bytes()))
for name in ['lean-toolchain','lake-manifest.json']:add(MAIN/'circuits'/name,'original-circuits/'+name)
add(Path(__file__),'assemble.py')
assert sum(p.stat().st_size for p in sources.values())<64*1024**2
rows=[{'archive_path':name,'original':pin(p)} for name,p in sorted(sources.items())]
manifest={'kind':'EXISTING_OFFICIAL_EXTERNAL_FLOOR08_LOSSLESS_DATA_TRANSPORT','selected_inventory':pin(floor),'modules':3612,'immutable_identity_records':20202,'entries':rows,'object_bytes_in_archive':0,'toolchain_bytes_in_archive':0,'proof_replay':False,'native_execution':False,'certification':False,'scope':'Existing exact floor08 and original floor06/composition/cache qualification provenance only. Official source and required object inventory/load-path identities retained unchanged. Optional current-host auxiliary objects remain identified as such. Identity does not establish semantic correspondence; no new proof/native/control result.'}
assert not (ROOT/'manifest.json').exists()
(ROOT/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
archive=ROOT/'portable-windows-external-floor08-data01.tar.xz';assert not archive.exists()
with tarfile.open(archive,'w:xz',preset=7) as tar:
    for name,p in sorted(sources.items()):
        b=p.read_bytes();info=tarfile.TarInfo(name);info.size=len(b);info.mode=0o644;info.mtime=0;tar.addfile(info,io.BytesIO(b))
    b=(ROOT/'manifest.json').read_bytes();info=tarfile.TarInfo('manifest.json');info.size=len(b);info.mode=0o644;info.mtime=0;tar.addfile(info,io.BytesIO(b))
with tarfile.open(archive,'r:xz') as tar:
    assert len(tar.getmembers())==len(rows)+1
    for row in rows:
        b=tar.extractfile(row['archive_path']).read();assert len(b)==row['original']['bytes'] and hashlib.sha256(b).hexdigest()==row['original']['sha256']
        assert pin(row['original']['path'])==row['original']
print(json.dumps({'archive':pin(archive),'manifest':pin(ROOT/'manifest.json'),'entries':len(rows),'no_proof_replay':True,'selected_inventory':pin(floor)}))
