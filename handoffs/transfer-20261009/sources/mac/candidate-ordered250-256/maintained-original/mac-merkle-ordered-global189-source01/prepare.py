from pathlib import Path
import sys,json,hashlib
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-merkle-ordered-global189-source01'
def require(v,m):
 if not v:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site and not sys.flags.optimize,'isolated')
require(not S.exists(),'fresh immutable source')
n='CapturedMerkleOrderedGlobal189'
b='''import ShielddSecurity.CapturedMerklePathGlobal187
import ShielddSecurity.CapturedMerkleBitsGlobal188
import ShielddSecurity.MerkleOrdered34
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleOrderedGlobal189
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
variable {F : Type} [Field F] [CharP F p]
theorem bit_encoding (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ bits : Fin 32 → Bool,∀ i : Fin 32,rho (184+i.val)=MerkleQuaternary30.boolValue (bits i) :=
 MerkleOrdered34.exists_bits rho (CapturedMerkleBitsGlobal188.rows_sound rho satisfied)
theorem ordered_anchor (rho : Nat → F) (one : rho 0=1)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ bits : Fin 32 → Bool,(∀ i : Fin 32,rho (184+i.val)=MerkleQuaternary30.boolValue (bits i)) ∧
 rho 4=MerkleOrdered34.root rho bits 16 := by
 obtain ⟨bits,encoding⟩ := bit_encoding rho satisfied
 refine ⟨bits,encoding,?_⟩
 rw [CapturedMerklePathGlobal187.anchor rho one satisfied,MerkleOrdered34.meaning_eq rho bits encoding 15 (by decide)]
end ShielddSecurity.CapturedMerkleOrderedGlobal189
'''
inputs={str(p):pin(p)for p in [W/'mac-merkle-path-global187-source01/source-root/ShielddSecurity/CapturedMerklePathGlobal187.lean',W/'mac-merkle-bits-global188-source01/source-root/ShielddSecurity/CapturedMerkleBitsGlobal188.lean',W/'mac-merkle-ordered34-source04/source-root/ShielddSecurity/MerkleOrdered34.lean']}
S.mkdir();(S/'generate.py').write_bytes((W/'mac-indexed-slices183-source01/generate.py').read_bytes());(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
with(S/'templates01.json').open('x')as f:f.write(json.dumps(dict(modules={n:dict(body=b,names=['bit_encoding','ordered_anchor'])},inputs=inputs,scope='SOURCE-only ordered16-level Merkle root plus actualBoolean encoding derived from full captured relation/rho0=1. No row-truth/hash-truth premise. Independent single-integer quaternary-position identity/native/full Transfer remain OPEN. All audits UNRUN.'),sort_keys=True,separators=(',',':'))+'\n')
