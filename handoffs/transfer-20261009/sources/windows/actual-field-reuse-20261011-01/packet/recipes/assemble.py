"""Read-only certificate reuse packet. Does not invoke Lean or modify evidence."""
import base64, hashlib, io, json, math, re, shutil, subprocess, tarfile
from pathlib import Path
ROOT = Path(__file__).resolve().parent
MAIN = Path('C:/src/shieldd-formal')
DIAG = MAIN / '.work/diagnostics'
OLD = DIAG / 'transfer-implementation-20261002/windows-field-concrete-20261009-01-kernel'
REV = subprocess.check_output(['git','rev-parse','origin/codex/security-assurance'],cwd=MAIN).decode().strip()
PACKET = ROOT / 'packet'
PACKET.mkdir(exist_ok=False)
def digest(b): return hashlib.sha256(b).hexdigest()
def put(name, data):
    path = PACKET / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)
    return {'path': name, 'bytes': len(data), 'sha256': digest(data)}
def git_file(name, path):
    data = subprocess.check_output(['git','show',REV+':'+path],cwd=MAIN)
    record = put(name,data)
    record['git_path'] = path
    record['git_revision'] = REV
    return data,record
base = 'handoffs/transfer-20261009/'
field,field_record = git_file('source/ConcreteJubjubField01.lean', base+'sources/windows/concrete-field-20261009-01/handwritten/ConcreteJubjubField01.lean')
retained,retained_record = git_file('retained/ConcreteJubjubField01.lean', base+'sources/windows/closed-cardinality-20261010-01/retained-import-context/ShielddSecurity/ConcreteJubjubField01.lean')
mac,mac_record = git_file('mac/CapturedFirstSubgroup81.lean',base+'sources/mac/subgroup-source78-81/source/ShielddSecurity/CapturedFirstSubgroup81.lean')
data,data_record = git_file('mac/TransferFirstSubgroupData01.lean',base+'sources/mac/mac-connected-subgroup01/final01/project/ShielddSecurity/TransferFirstSubgroupData01.lean')
constructor,constructor_record = git_file('mac/CapturedFourSubgroupConstructor88.lean',base+'sources/mac/four-subgroup-constructor86-89/source/ShielddSecurity/CapturedFourSubgroupConstructor88.lean')
published_receipt,receipt_record = git_file('receipts/published-concrete-field.json',base+'receipts/windows/concrete-field-20261009-01.json')
audit = json.loads((OLD/'ConcreteJubjubField01/audit.json').read_text())
published = json.loads(published_receipt)['runs']['concrete01']['modules']['ConcreteJubjubField01']
assert audit == published['audit'] and published['actual_exit'] == 0
assert digest(field) == audit['original_source_sha256']
assert digest((OLD/'project/ShielddSecurity/ConcreteJubjubField01.lean').read_bytes()) == audit['candidate_sha256']
assert digest((OLD/'ConcreteJubjubField01/stdout.txt').read_bytes()) == published['stdout_sha256']
assert not (OLD/'ConcreteJubjubField01/stderr.txt').read_bytes()
assert (OLD/'ConcreteJubjubField01/exit.txt').read_text().strip() == '0'
assert audit['audits'] == 10 and audit['full_types_checked']
allowed = {'propext','Classical.choice','Quot.sound'}
assert all(set(a) <= allowed for a in audit['axioms'].values())
literal = lambda b,n: int(re.search(rb'^def '+n.encode()+rb'\s*:\s*(?:Nat|Int)\s*:=\s*(\d+)',b,re.M)[1])
d = literal(mac,'d'); coefficient = literal(field,'coefficientNat')
p = literal(data,'p')
scalar = Path('C:/src/shieldd-transfer-windows-publication-20261009/circuits/ShielddSecurity/Scalar.lean')
scalar_bytes = scalar.read_bytes()
modulus = literal(scalar_bytes,'modulus')
assert d == coefficient == literal(retained,'coefficientNat')
assert p == modulus
imaginary = literal(field,'imaginaryNat')
assert imaginary == literal(retained,'imaginaryNat')
assert (imaginary*imaginary+1) % p == 0
assert pow(d,(p-1)//2,p) == p-1
put('source/Scalar.lean',scalar_bytes)
originals=[]
for relative in ['manifest.json','recipe.json','project/ShielddSecurity/ConcreteJubjubField01.lean','ConcreteJubjubField01/audit.json','ConcreteJubjubField01/stdout.txt','ConcreteJubjubField01/stderr.txt','ConcreteJubjubField01/exit.txt','ConcreteJubjubField01/start.txt','ConcreteJubjubField01/end.txt','ConcreteJubjubField01/memory.txt']:
    b=(OLD/relative).read_bytes()
    r=put('original/'+relative,b)
    r['original_path']=str(OLD/relative)
    originals.append(r)
obj=OLD/'project/ShielddSecurity/ConcreteJubjubField01.olean'
object_bytes=obj.read_bytes()
assert len(object_bytes)==102592 and digest(object_bytes)=='b2ee627636373e575e0e7cdc962a9eb05d85f3db699fea0cc88f9cf40ce48c1b'
pool_obj=DIAG/'transfer-base-order-owned-floor-20261010-02/modules/ShielddSecurity/ConcreteJubjubField01.olean'
assert pool_obj.read_bytes()==object_bytes
review={
 'kind':'READ_ONLY_ACTUAL_FIELD_CERTIFICATE_REUSE', 'canonical_revision':REV,
 'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a',
 'fresh_proof_credit':0, 'fresh_lean_processes':0, 'fresh_runtime_controls':0,
 'existing_audits':10,'certificates_selected':['ShielddSecurity.ConcreteJubjubField01.coefficient_no_unit_square','ShielddSecurity.ConcreteJubjubField01.imaginary_square'],
 'literal_comparison':{'captured_d_Int':d,'coefficientNat':coefficient,'captured_p_Nat':p,'Scalar_modulus':modulus,'imaginaryNat':imaginary,'d_equal':True,'p_equal':True},
 'integer_sanity_checks':{'imaginary_square_plus_one_mod_p':0,'euler_residue':p-1,'proof_credit':0},
 'instantiation':{'F':'ShielddSecurity.ConcreteJubjubField01.F','imaginary':'ShielddSecurity.ConcreteJubjubField01.imaginary','charP':'Existing ZMod field instance; captured p and Scalar.modulus have equal literal definitions.','nonsquare':'coefficient_no_unit_square; constructor d is an Int cast, coefficient is a Nat cast. Mac must check the short cast normalization in its existing constructor closure.','square_minus_one':'imaginary_square directly'},
 'remaining':'No new theorem binding CapturedFirstSubgroup81.d to coefficient was compiled here. Cast normalization and constructor application belong to the Mac global constructor module. Native field/coordinate/FFI correspondence and full Transfer remain open.',
 'originals':originals,'canonical_sources':[field_record,retained_record,mac_record,data_record,constructor_record,receipt_record],
 'object_identity_only':{'path':str(obj),'copy':str(pool_obj),'bytes':len(object_bytes),'sha256':digest(object_bytes),'payload_included':False},
 'qualification':'Original exit, complete full-type stdout, audit census and standard axioms match the published receipt. Source and object hashes establish identity, not native semantic correspondence.'}
put('review.json',(json.dumps(review,indent=2,sort_keys=True)+'\n').encode())
put('recipes/assemble.py',Path(__file__).read_bytes())
files=[{'path':str(p.relative_to(PACKET)).replace('\\','/'),'bytes':p.stat().st_size,'sha256':digest(p.read_bytes())} for p in sorted(PACKET.rglob('*')) if p.is_file()]
put('manifest.json',(json.dumps({'kind':review['kind'],'files':files,'fresh_proof_credit':0},indent=2,sort_keys=True)+'\n').encode())
archive=ROOT/'portable-windows-actual-field-certificate-reuse01.tar.xz'
assert not archive.exists()
with tarfile.open(archive,'w:xz',preset=6) as tf:
    for p in sorted(PACKET.rglob('*')):
        if p.is_file():
            b=p.read_bytes(); info=tarfile.TarInfo(str(p.relative_to(PACKET)).replace('\\','/')); info.size=len(b); info.mode=0o644; info.mtime=0
            tf.addfile(info,io.BytesIO(b))
with tarfile.open(archive,'r:xz') as tf:
    for member in tf.getmembers(): assert tf.extractfile(member).read()==(PACKET/member.name).read_bytes()
b=archive.read_bytes(); encoded=base64.b64encode(b).decode(); count=math.ceil(len(encoded)/12000)
transport={'transport':'windows-actual-field-certificate-reuse01','archive_bytes':len(b),'archive_sha256':digest(b),'parts':count,'base64_chars':len(encoded)}
for index in range(count):
    chunk=encoded[index*12000:(index+1)*12000]
    (ROOT/f'part-{index+1:02}.json').write_text(json.dumps(dict(transport,part=index+1,chunk_sha256=digest(chunk.encode()),base64=chunk)))
(ROOT/'transport.json').write_text(json.dumps(transport,indent=2)+'\n')
print(json.dumps(dict(transport,manifest_bytes=(PACKET/'manifest.json').stat().st_size,manifest_sha256=digest((PACKET/'manifest.json').read_bytes()),review_sha256=digest((PACKET/'review.json').read_bytes()),members=len(files)+1)))
