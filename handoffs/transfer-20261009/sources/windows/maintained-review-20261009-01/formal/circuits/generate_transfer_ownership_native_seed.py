"""Bind the first actual ownership double to globally read native coordinates.

Requires accepted metadata/row selection and the independently checked local
constructor. Actual SDK address/issuer argument routing is a source contract;
no native coordinate or computed output is a per-witness theorem premise.
"""
from . import transfer_ownership_completion as completion
from . import generate_transfer_ownership_double_completion as double
from .generate_hash_round import _signature_audits


def generate(checked,extracted,readonly_lcs=()):
    local_name,_=double.generate(checked,extracted,readonly_lcs)
    cones=completion.owner.cone_certificates(checked,extracted,0,True)
    return render_seed(checked,cones,local_name)


def render_seed(checked,cones,local_name):
    """Neutral exact singleton/native input seed after strict source ingress."""
    cone=next(cone for cone in cones['cones'] if cone['role']=='formula0')
    inputs=[cones['observations'][identity][1] for identity in cone['inputs']]
    if len(inputs)!=2 or any(len(terms)!=1 or terms[0][1]!=1 for terms in inputs):
        raise completion.relation.RelationError('ownership native seed exact source coordinate singletons')
    x,y=[terms[0][0] for terms in inputs];copy=checked['metadata']['constant_copy']
    if x==y or any(column in (0,copy) for column in (x,y)):
        raise completion.relation.RelationError('ownership native source coordinate/copy separation')
    name=local_name+'NativeSeed';c=local_name.removesuffix('Completion')+'Cones'
    source=f'''import ShielddSecurity.{local_name}
import ShielddSecurity.ShielddPointCoordinateSeed
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
variable {{F : Type}} [Field F] [CharP F {local_name}.modulus]
variable {{E S R K Q Signing J : Type}} [AddCommGroup J]
variable (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
variable (model : Group.StandardCurveModel J ({c}.coefficientD : F))
variable (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr ({c}.coefficientD : F) model)
variable {{Encoded Native : Type}} (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
variable (point : S) (base : Nat → F)
def seeded : Nat → F := ShielddPointCoordinateSeed.seed fq fr ({c}.coefficientD : F)
  model upstream backend point {x} {y} base
def completed : Nat → F := {local_name}.completed (seeded fq fr model upstream backend point base)
theorem seeded_input : {local_name}.inputPoint (seeded fq fr model upstream backend point base) =
    model.coordinates (upstream.embed (upstream.promote point)) := by
  have coordinates := ShielddPointCoordinateSeed.coordinates fq fr ({c}.coefficientD : F)
    model upstream backend point {x} {y} (by decide) base
  simpa only [seeded,{local_name}.inputPoint,{local_name}.inputX,{local_name}.inputY,eval,
    Int.cast_one,one_mul,mul_one,add_zero] using coordinates
theorem native_double_complete (imaginary : F)
    (nonSquare : Group.NoUnitSquare ({c}.coefficientD : F)) (imaginarySquare : imaginary*imaginary = -1)
    (one : base 0 = 1) (linked : base {copy} = base 0) :
    Satisfies (completed fq fr model upstream backend point base) ({c}.rawRows ++ {local_name}.quotientRaw) ∧
      {local_name}.outputPoint (completed fq fr model upstream backend point base) =
        model.coordinates (2 • upstream.embed (upstream.promote point)) := by
  let seed := seeded fq fr model upstream backend point base
  have seedOne : seed 0 = 1 :=
    (ShielddPointCoordinateSeed.seed_preserves fq fr ({c}.coefficientD : F)
      model upstream backend point {x} {y} base 0 (by decide)).trans one
  have seedLink : seed {copy} = seed 0 := by
    dsimp only [seed,seeded]
    rw [ShielddPointCoordinateSeed.seed_preserves fq fr ({c}.coefficientD : F)
      model upstream backend point {x} {y} base {copy} (by decide),
      ShielddPointCoordinateSeed.seed_preserves fq fr ({c}.coefficientD : F)
      model upstream backend point {x} {y} base 0 (by decide),linked]
  have input : {local_name}.inputPoint seed = model.coordinates (upstream.embed (upstream.promote point)) :=
    seeded_input fq fr model upstream backend point base
  have valid : Group.OnCurve ({c}.coefficientD : F) ({local_name}.inputPoint seed) := by
    rw [input]; exact model.onCurve _
  have result := {local_name}.actual_point_complete imaginary nonSquare imaginarySquare seed seedOne seedLink valid
  refine ⟨result.1,?_⟩
  change {local_name}.outputPoint ({local_name}.completed seed) =
    model.coordinates (2 • upstream.embed (upstream.promote point))
  rw [two_nsmul,model.addition,← input]
  exact result.2.1
#print axioms seeded_input
#print axioms native_double_complete
end ShielddSecurity.{name}
'''
    return name,_signature_audits(source)
