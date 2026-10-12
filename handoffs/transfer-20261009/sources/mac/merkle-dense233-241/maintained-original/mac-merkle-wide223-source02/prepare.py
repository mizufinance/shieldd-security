from pathlib import Path
import json,hashlib,sys,re,os
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-merkle-global-arithmetic184-source01';S=W/'mac-merkle-wide223-source02'
def require(c,m):
 if not c:raise RuntimeError(m)
def pin(p):
 b=Path(p).read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated preparation');require(not S.exists(),'fresh bounded pilot source');gen=json.loads((P/'generation01.json').read_bytes());outputs={x['name']:x['source']for x in gen['outputs']};inputs={str(P/'generation01.json'):pin(P/'generation01.json')};starts=[]
for i in range(22,24):
 n='CapturedMerkleGlobalArithmetic184L01B'+str(i).zfill(2);v=outputs[n];p=Path(v['path']);require(pin(p)==v,'exact prior SOURCE association');text=p.read_text();m=re.search(r'def rows : List Row := \(MerkleGlobalBody181.arithmeticRows 1\).drop (\d+) \|>.take 16',text);q=re.search(r'def indices : List Nat := List.range\x27 (\d+) 16',text);require(m and q and int(m[1])==16*i,'exact existing target slices');starts.append(int(q[1]));inputs[str(p)]=v
require(starts==list(range(starts[0],starts[0]+32,16)),'exact contiguous capture positions');first=starts[0]
body='''import ShielddSecurity.MerkleGlobalBody181
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleWide223Pilot
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def rows : List Row := (MerkleGlobalBody181.arithmeticRows 1).drop 352 |>.take 32
def indices : List Nat := List.range' '''+str(first)+''' 32
def productionCheck : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by decide +kernel
theorem count : rows.length=32 := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho rows := CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
 ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedMerkleWide223Pilot
'''
names=['rows','indices','productionCheck','checked','count','sound'];st=os.statvfs(W);require(st.f_bavail*st.f_frsize>2*1024**3+1048576,'disk reserve');S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-shared-word-flags220-source04/generate.py').read_bytes());(S/'templates01.json').write_text(json.dumps(dict(modules={'CapturedMerkleWide223Pilot':dict(body=body,names=names)},inputs=inputs,scope='SOURCE_ONLY_UNRUN throughput pilot. Same finite production identity checker and arbitrary-assignment semantic bridge as original16-row providers, covering32 late-tail rows. Existing unqualified SOURCE slice expressions provide target DATA only; future kernel checked proves exact row/copy normalization. No old module replay, no assertion truth or desired hash premise; physical limits unchanged. Pilot success permits maintained larger symbolic partition, not automatic full path closure.'),sort_keys=True,separators=(',',':'))+'\n')
