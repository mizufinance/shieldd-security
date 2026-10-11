from pathlib import Path
import json,hashlib,sys
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-subgroup-seed-completion203-source03'
def require(v,m):
 if not v:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags');require(not S.exists(),'immutable source')
body='''import ShielddSecurity.SubgroupPreimage202
import ShielddSecurity.RegistryPointSemantic200
import ShielddSecurity.CapturedFourSubgroupSeed89
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SubgroupSeedCompletion203
open PoseidonNatural192
variable {F J : Type} [Field F] [AddCommGroup J]
def fieldPoint (point : TransferCore.Affine) : Group.Point F := ⟨(point.x:F),(point.y:F)⟩
theorem member_of_valid (c : TransferSem.Crypto) (representation : CanonicalRepresentation F)
 {d : F} (model : Group.StandardCurveModel J d) (point : TransferCore.Affine)
 (valid : TransferSem.ValidPoint (RegistryPointSemantic200.interpret c representation model) point) :
 CapturedSubgroupModel199.Member model (fieldPoint point) := by
 rcases valid.2 with ⟨represented,encoded,killed⟩
 refine ⟨represented,?_,killed⟩
 have hx : (model.coordinates represented).x=(fieldPoint point).x := by
   have same:=congrArg TransferCore.Affine.x encoded
   exact (representation.cast_value _).symm.trans (congrArg (fun n : Nat => (n:F)) same)
 have hy : (model.coordinates represented).y=(fieldPoint point).y := by
   have same:=congrArg TransferCore.Affine.y encoded
   exact (representation.cast_value _).symm.trans (congrArg (fun n : Nat => (n:F)) same)
 have point_ext : ∀ left right : Group.Point F,
   left.x=right.x → left.y=right.y → left=right := by
   intro left right xEq yEq
   cases left
   cases right
   cases xEq
   cases yEq
   rfl
 exact point_ext _ _ hx hy
theorem exists_initial (model : Group.StandardCurveModel J (CapturedFirstSubgroup81.d:F))
 (imaginary : F) (nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F))
 (imaginarySquare : imaginary*imaginary = -1) (base : Nat → F)
 (members : ∀ group,CapturedSubgroupModel199.Member model (CapturedFourSubgroupSeed89.Claimed base group)) :
 ∃ initial : Fin 4 → Group.Point F,
 (∀ group,Group.OnCurve (CapturedFirstSubgroup81.d:F) (initial group)) ∧
 ∀ group,CapturedFourSubgroupSeed89.Claimed base group=
   CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) (initial group) := by
 classical
 have preimages:=fun group => SubgroupPreimage202.member_preimage (CapturedFirstSubgroup81.d:F)
   imaginary nonSquare imaginarySquare model _ (members group)
 refine ⟨fun group => Classical.choose (preimages group),?_,?_⟩
 · intro group
   exact (Classical.choose_spec (preimages group)).1
 · intro group
   exact (Classical.choose_spec (preimages group)).2.symm
variable [CharP F TransferFirstSubgroupData01.p]
theorem constructor (model : Group.StandardCurveModel J (CapturedFirstSubgroup81.d:F))
 (imaginary : F) (nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F))
 (imaginarySquare : imaginary*imaginary = -1) (base : Nat → F)
 (one : base 0=1) (linked : base TransferFirstSubgroupData01.copy=base 0)
 (members : ∀ group,CapturedSubgroupModel199.Member model (CapturedFourSubgroupSeed89.Claimed base group)) :
 ∃ initial : Fin 4 → Group.Point F,
 CompilerArithmeticBlock44.SatisfiesAt (CapturedFourSubgroupSeed89.completed base initial)
   CapturedFullArithmetic52.rowAt 177954 ∧
 (∀ group,Satisfies (CapturedFourSubgroupSeed89.completed base initial)
   (CapturedFourSubgroupConstructor88.originalRows group)) ∧
 ∀ column,(column<22738 ∨ 200692≤column) → column∉CapturedFourSubgroupSeed89.hintColumns →
   CapturedFourSubgroupSeed89.completed base initial column=base column := by
 obtain ⟨initial,valid,binding⟩:=exists_initial model imaginary nonSquare imaginarySquare base members
 exact ⟨initial,CapturedFourSubgroupSeed89.arithmetic base initial,
   CapturedFourSubgroupSeed89.all_four base initial imaginary one linked binding valid nonSquare imaginarySquare,
   fun column outside unseeded => CapturedFourSubgroupSeed89.outside base initial column outside unseeded⟩
end ShielddSecurity.SubgroupSeedCompletion203
'''
pins=[W/'mac-subgroup-seed-completion203-source02/producer-manifest01.json',W/'mac-subgroup-seed-completion203-source01/producer-manifest01.json',W/'mac-subgroup-preimage202-source02/source-root/ShielddSecurity/SubgroupPreimage202.lean',W/'mac-registry-point-semantic200-source01/source-root/ShielddSecurity/RegistryPointSemantic200.lean',W/'mac-four-subgroup-seed89-source05/source-root/ShielddSecurity/CapturedFourSubgroupSeed89.lean']
S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-indexed-slices183-source01/generate.py').read_bytes())
(S/'templates01.json').write_text(json.dumps(dict(modules={'SubgroupSeedCompletion203':dict(body=body,names=['fieldPoint','member_of_valid','exists_initial','constructor'])},inputs={str(p):pin(p)for p in pins},scope='SOURCE_ONLY_UNRUN. Lawful interpreted point membership derives exact field-coordinate member; independent nonsquare/imaginary/model plus four lawful memberships construct all four cofactor preimages, then one assignment satisfying all177954 arithmetic and the four qualified subgroup original-row families. No desired preimage, target row satisfaction, or hash truth premise; explicit input copy/zero and exact 20hint frame. No assertion/global legal-Transfer/native closure. Four planned reports.'),sort_keys=True,separators=(',',':'))+'\n')
