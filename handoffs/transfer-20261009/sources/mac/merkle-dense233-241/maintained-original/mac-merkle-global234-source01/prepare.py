from pathlib import Path
import json,hashlib,sys,os
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-merkle-local229-source03';S=W/'mac-merkle-global234-source01';C=W/'mac-merkle-thin233-source01'
def require(c,m):
 if not c:raise RuntimeError(m)
def pin(p):
 b=Path(p).read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated source preparation');require(not S.exists(),'new immutable source');old=json.loads((P/'templates01.json').read_bytes())['modules']['CapturedMerkleLocal229Pilot']['body'];a=old.index('theorem parent_equal');z=old.index('\ntheorem check_congr',a);parent=old[a:z];body='''import ShielddSecurity.CapturedMerkleLocal233Certificate
import ShielddSecurity.CapturedMerkleLocal229Single
import ShielddSecurity.MerkleGlobalBody181
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B20
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def rows : List Row := CapturedMerkleLocal233Certificate.rows
theorem rows_exact : rows=((MerkleGlobalBody181.arithmeticRows 1).drop 320 |>.take 16) := by rfl
def indices : List Nat := CapturedMerkleLocal233Certificate.indices
def localParent : Nat → Option Row := CapturedMerkleLocal233Certificate.localParent
'''+parent+'''\ndef productionCheck : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by
 change CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows=true
 rw [CapturedMerkleLocal229Single.check_congr CapturedFullRelation58.rowAt localParent indices rows parent_equal]
 exact CapturedMerkleLocal233Certificate.local_checked
theorem count : rows.length=16 := CapturedMerkleLocal233Certificate.count
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) : Satisfies rho rows :=
 CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
  ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B20
''';inputs={str(P/'templates01.json'):pin(P/'templates01.json')};g=json.loads((C/'generation01.json').read_bytes());inputs[g['outputs'][0]['source']['path']]=g['outputs'][0]['source'];require(os.statvfs(W).f_bavail*os.statvfs(W).f_frsize>2*1024**3+1048576,'disk reserve');S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((P/'generate.py').read_bytes());(S/'templates01.json').write_text(json.dumps(dict(modules={'CapturedMerkleGlobalArithmetic184L01B20':dict(body=body,names=['rows','rows_exact','indices','localParent','parent_equal','productionCheck','checked','count','sound'])},inputs=inputs,scope='SOURCE_ONLY_UNRUN symbolic full-captured association for sixteen dense rows after independent narrow-import local certificate. Uses exact rfl original positional equality and checked generic congruence; no global finite evaluation, no initial row truth/hash desired premise. Original six declarations retain original meaning; three transparent transport declarations additionally audited.'),sort_keys=True,separators=(',',':'))+'\n')
