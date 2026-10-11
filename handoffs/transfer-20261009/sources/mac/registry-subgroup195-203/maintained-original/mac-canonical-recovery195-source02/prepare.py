from pathlib import Path
import json,hashlib,sys
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-canonical-recovery195-source02'
def require(v,m):
 if not v:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags');require(not S.exists(),'immutable source')
b='''import ShielddSecurity.PoseidonNatural192
import ShielddSecurity.CapturedEpochHints62
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CanonicalRecovery195
open PoseidonNatural192
open CompilerArithmeticTransport41 (p)
variable {F : Type} [Field F] [CharP F p]
theorem value_unique (representation : CanonicalRepresentation F) (x : F) (n : Nat)
 (bound : n<p) (equal : (n:F)=x) : representation.value x=n :=
 CapturedEpochHints62.cast_small_unique _ n (representation.bounded x) bound
   ((representation.cast_value x).trans equal.symm)
theorem value_cast (representation : CanonicalRepresentation F) (n : Nat) (bound : n<p) :
 representation.value (n:F)=n := value_unique representation (n:F) n bound rfl
theorem nat_cast_iff (left right : Nat) (leftBound : left<p) (rightBound : right<p) :
 (left:F)=(right:F) ↔ left=right :=
 ⟨CapturedEpochHints62.cast_small_unique left right leftBound rightBound,fun h => congrArg (fun n : Nat => (n:F)) h⟩
omit [CharP F p] in
theorem value_injective (representation : CanonicalRepresentation F) (x y : F)
 (equal : representation.value x=representation.value y) : x=y :=
 (representation.cast_value x).symm.trans
   ((congrArg (fun n : Nat => (n:F)) equal).trans (representation.cast_value y))
theorem fold_bound (items : List Nat) (step : Nat → Nat → Nat)
 (bounded : ∀ node level,step node level<TransferCore.fieldModulus) (initial : Nat)
 (initialBound : initial<TransferCore.fieldModulus) :
 items.foldl step initial<TransferCore.fieldModulus := by
 induction items generalizing initial with
 | nil => exact initialBound
 | cons head tail ih =>
   exact ih (step initial head) (bounded initial head)
omit [CharP F p] in
theorem treeRoot_bound (c : TransferSem.Crypto) (small : Poseidon.Parameters F 3)
 (wide : Poseidon.Parameters F 6) (representation : CanonicalRepresentation F)
 (domain : TransferSem.Domain) (depth position leaf : Nat) (siblings : Nat → Fin 3 → Nat)
 (leafBound : leaf<TransferCore.fieldModulus) :
 TransferSem.treeRoot (withHash c small wide representation) domain depth position leaf siblings<TransferCore.fieldModulus := by
 unfold TransferSem.treeRoot
 apply fold_bound
 · intro node level
   exact representation.bounded _
 · exact leafBound
theorem treeRoot_eq_of_cast (c : TransferSem.Crypto) (small : Poseidon.Parameters F 3)
 (wide : Poseidon.Parameters F 6) (representation : CanonicalRepresentation F)
 (domain : TransferSem.Domain) (depth position leaf claimed : Nat) (siblings : Nat → Fin 3 → Nat)
 (leafBound : leaf<TransferCore.fieldModulus) (claimedBound : claimed<TransferCore.fieldModulus)
 (fieldEqual : treeRoot small wide domain depth position (leaf:F)
   (fun level slot => (siblings level slot:F))=(claimed:F)) :
 TransferSem.treeRoot (withHash c small wide representation) domain depth position leaf siblings=claimed := by
 apply CapturedEpochHints62.cast_small_unique (F:=F) _ claimed
   (treeRoot_bound c small wide representation domain depth position leaf siblings leafBound) claimedBound
 exact (treeRoot_cast c small wide representation domain depth position leaf siblings).trans fieldEqual
end ShielddSecurity.CanonicalRecovery195
'''
S.mkdir();(S/'generate.py').write_bytes((W/'mac-indexed-slices183-source01/generate.py').read_bytes());(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
pins=[W/'mac-canonical-recovery195-source01/producer-manifest01.json',W/'mac-poseidon-natural192-source02/source-root/ShielddSecurity/PoseidonNatural192.lean',W/'mac-first-epoch-hints62-source03/source-root/ShielddSecurity/CapturedEpochHints62.lean']
(S/'templates01.json').write_text(json.dumps(dict(modules={'CanonicalRecovery195':dict(body=b,names=['value_unique','value_cast','nat_cast_iff','value_injective','fold_bound','treeRoot_bound','treeRoot_eq_of_cast'])},inputs={str(p):pin(p)for p in pins},scope='SOURCE-only generic canonical recovery and integer tree-root lifting. Canonical representation laws explicit; tree root field equality is the independent lower-layer certificate interface, not assumed final Transfer truth. No concrete field/native/captured row/Transfer completion claim; seven audits UNRUN.'),sort_keys=True,separators=(',',':'))+'\n')
