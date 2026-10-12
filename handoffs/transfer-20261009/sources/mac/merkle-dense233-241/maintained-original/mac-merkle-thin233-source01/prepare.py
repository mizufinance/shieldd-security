from pathlib import Path
import json,hashlib,sys,os,runpy
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-merkle-local229-source03';S=W/'mac-merkle-thin233-source01';E=W/'mac-full-arithmetic45-execution258'
def require(c,m):
 if not c:raise RuntimeError(m)
def pin(p):
 b=Path(p).read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated preparation');require(not S.exists(),'fresh immutable source');v=json.loads((P/'templates01.json').read_bytes());require(pin(P/'templates01.json')==json.loads((P/'producer-manifest01.json').read_bytes())['templates01.json'],'exact maintained predecessor');old=v['modules']['CapturedMerkleLocal229Pilot']['body'];a=old.index('def rows :');z=old.index('\ntheorem rows_exact',a);rows=old[a:z];a=old.index('def indices :');z=old.index('\ntheorem parent_equal',a);checking=old[a:z];body='''import ShielddSecurity.MerkleFamily32Tables
import ShielddSecurity.CapturedRegistryTail22
import ShielddSecurity.CapturedArithmetic45B0018
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleLocal233Certificate
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
'''+rows+'\n'+checking+'''\ntheorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleLocal233Certificate
''';names=['rows','indices','localParent','localCheck','local_checked','count'];g=runpy.run_path(str(E/'maintained/guard.py'),run_name='SOURCE_ONLY_READ');c=g['read_config'](str(E/'config01.json'),pin(E/'config01.json')['sha256']);imports=json.loads(Path(c['closure']['path']).read_bytes())['modules'];imports.update(c['qualified_batch_imports']);inputs={str(P/'templates01.json'):pin(P/'templates01.json')}
for n in ['MerkleFamily32Tables','CapturedRegistryTail22','CapturedArithmetic45B0018','CompilerIndexedCopyStream171']:
 record=imports[n];require(pin(record['source']['path'])==record['source'],'exact qualified source');inputs[record['source']['path']]=record['source']
require('CapturedFullRelation58'not in body and 'MerkleGlobalBody181'not in body,'no whole599 provider imported through this direct source');require(os.statvfs(W).f_bavail*os.statvfs(W).f_frsize>2*1024**3+1048576,'disk reserve');S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((P/'generate.py').read_bytes());(S/'templates01.json').write_text(json.dumps(dict(modules={'CapturedMerkleLocal233Certificate':dict(body=body,names=names)},inputs=inputs,scope='SOURCE_ONLY_UNRUN same sixteen dense rows3890..3905 and exact local original-row branches, finite canonical/copy identity checker. Full599/global relation removed from local certificate direct imports; global source-row association deferred to symbolic wrapper, not assumed. Original failed attempts preserved; same heap/per-run limits.'),sort_keys=True,separators=(',',':'))+'\n')
