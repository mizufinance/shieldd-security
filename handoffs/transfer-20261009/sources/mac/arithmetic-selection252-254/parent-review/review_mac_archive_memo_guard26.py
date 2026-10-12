"""Independent exact-source memo guard review and isolated primitive controls."""
from pathlib import Path
import ast,hashlib,json,lzma,os,runpy,tempfile,datetime
J=Path(__file__).resolve().parent;W=J.parent;old=W/'mac-full-arithmetic45-execution265/maintained/guard.py';memo=W/'mac-full-arithmetic45-execution267/maintained/guard.py';S=W/'mac-archive-absence246-source02';new=S/'guard.py'
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
assert pin(old)['sha256']=='69ba105cdcb31ceff1c62aa565f9b680ae561a681728aa4235ed2a6268de77af'
assert pin(memo)['sha256']=='d0d0d2c9058d660591e40eac1aded7106d3c9d2ce94b219f17f115bd2c036af8'
assert pin(new)['sha256']=='c2b29e87f380508edf00219d7832c1db0bb8dc68b286cfd89c9e7c285a975faa'
def functions(p):return {n.name:ast.dump(n,include_attributes=False)for n in ast.parse(p.read_text()).body if isinstance(n,ast.FunctionDef)}
a,b,c=map(functions,[old,memo,new]);assert set(a)==set(b)==set(c)
assert [k for k in a if a[k]!=b[k]]==['checked_pin','checked_phase_close','fixed_check','bounds']
assert [k for k in b if b[k]!=c[k]]==['checked_pin','checked_phase_close']
for rel,v in json.loads((S/'producer-manifest01.json').read_text()).items():
 p=S/rel
 if 'symlink_target' in v:assert p.is_symlink() and os.readlink(p)==v['symlink_target'] and pin(p.resolve())==v['target']
 else:assert pin(p)==v
controls=[]
with tempfile.TemporaryDirectory(prefix='root-archive-memo26-')as tmp:
 for case in ['unchanged','wrong-original','exact-original','symlink-present','symlink-dangling','archive-change','ordinary-change','conflicting-pin']:
  root=Path(tmp)/case;root.mkdir();original=root/'original';archive=root/'archive.xz';raw=b'{}\n';archive.write_bytes(lzma.compress(raw));identity=dict(path=str(original),bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest());record=dict(original=identity,archive=pin(archive))
  env=runpy.run_path(str(new))['checked_pin'].__globals__;env['_STORAGE']={str(original):record};env['checked_pin'](identity);env['checked_phase_close']()
  if case=='wrong-original':original.write_bytes(b'bad')
  if case=='exact-original':original.write_bytes(raw)
  if case=='symlink-present':(root/'target').write_bytes(raw);original.symlink_to('target')
  if case=='symlink-dangling':original.symlink_to('missing')
  if case=='archive-change':st=archive.stat();archive.write_bytes(archive.read_bytes());os.utime(archive,ns=(st.st_atime_ns,st.st_mtime_ns))
  if case=='ordinary-change':
   other=root/'ordinary';other.write_bytes(b'one');env['checked_pin'](pin(other));st=other.stat();other.write_bytes(b'two');os.utime(other,ns=(st.st_atime_ns,st.st_mtime_ns))
  if case=='conflicting-pin':identity={**identity,'sha256':'0'*64}
  for op in ['cached','terminal']:
   if case in ['archive-change','ordinary-change','conflicting-pin'] and op=='cached' and case!='conflicting-pin':continue
   if case=='conflicting-pin' and op=='terminal':continue
   try:
    env['checked_pin'](identity)if op=='cached'else env['checked_phase_close']()
    assert case=='unchanged',(case,op);controls.append(dict(case=case,op=op,passed=True))
   except RuntimeError as e:
    assert case!='unchanged';controls.append(dict(case=case,op=op,refused=str(e)))
storage=W/'mac-history-metadata-preservation126-36/archive-map01.json';table=json.loads(storage.read_text())['records'];archives={}
for key,r in table.items():
 p=Path(key);assert not p.exists() and not p.is_symlink(),key
 a=Path(r['archive']['path']);assert not a.is_symlink() and pin(a)==r['archive'];archives[str(a)]=r['archive']
deployed=W/'mac-full-arithmetic45-execution270/maintained/guard.py';assert deployed.read_bytes()==new.read_bytes()
r=dict(status='PASSED',kind='Exact immutable memo/absence successor and independent isolated pure controls; no Lean',old=pin(old),memo=pin(memo),successor=pin(new),deployed=pin(deployed),source=pin(S/'prepare.py'),original_controls=pin(S/'controls01.json'),root_controls=controls,storage_map=pin(storage),originals_currently_absent=len(table),archive_pins=list(archives.values()),historical_reconciliation='Guard267 original weakness retained with reproducer. Root independently rehashed selected original sources, objects, full audit reports, receipts, inherited load/config/archive identities and machine observations in registry import audit; archived originals are still absent and exact archives retained. No accepted proof replay or alteration is needed to authenticate these immutable historical results. New future guard rejects even exact-byte original reappearance and dangling symlinks at both cached access and terminal close.',physical_limits='UNCHANGED; all functions except identified identity memo/phase closures are AST-identical; one verifier per host',full_transfer='OPEN',root_verifier_execution='NONE',time_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(J/'mac-archive-memo-absence-guard-review26.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:r[k]for k in ['status','originals_currently_absent','full_transfer']}|dict(root_controls=len(controls),archive_pins=len(archives))))
