from pathlib import Path
import json,sys,hashlib,os
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-indexed-chunks232-source01'
def require(c,m):
 if not c:raise RuntimeError(m)
def pin(p):
 b=Path(p).read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated preparation');require(not S.exists(),'fresh immutable source')
body='''import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.CompilerIndexedCopyChunks232
open CompilerIndexedCopyStream171
theorem check_append (p copy : Nat) (parent : Nat → Option Row) (fullLength : Nat)
 (indices later : List Nat) (rows rest : List Row) (count : indices.length=rows.length) :
 check p copy parent fullLength (indices++later) (rows++rest)=
 (check p copy parent fullLength indices rows && check p copy parent fullLength later rest) := by
 induction indices generalizing rows with
 | nil =>
   cases rows with
   | nil => rfl
   | cons row rows => simp only [List.length_nil,List.length_cons] at count; omega
 | cons position indices ih =>
   cases rows with
   | nil => simp only [List.length_nil,List.length_cons] at count; omega
   | cons row rows =>
     have smaller : indices.length=rows.length := Nat.succ.inj count
     simp only [List.cons_append,check,ih rows smaller,Bool.and_assoc]
end ShielddSecurity.CompilerIndexedCopyChunks232
'''
inputs={str(p):pin(p)for p in[W/'mac-indexed-copy-stream171-source01/source-root/ShielddSecurity/CompilerIndexedCopyStream171.lean']};require(os.statvfs(W).f_bavail*os.statvfs(W).f_frsize>2*1024**3+1048576,'disk reserve');S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-shared-word-flags220-source04/generate.py').read_bytes());(S/'templates01.json').write_text(json.dumps(dict(modules={'CompilerIndexedCopyChunks232':dict(body=body,names=['check_append'])},inputs=inputs,scope='SOURCE_ONLY_UNRUN generic symbolic composition of two finite indexed checker certificates with exact left length. No row truth/native/desired hash premises. Enables separately kernel-reduced dense chunks without whole-check interpreter memory accumulation.'),sort_keys=True,separators=(',',':'))+'\n')
