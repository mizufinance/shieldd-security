"""Actual ownership assignment bound to a constructed/viewed SDK address.

Admission is the owned native payment_address or views_address program. Raw
Transfer preparation success cannot supply either guard in the unregulated
branch. NK/AK and full caller/FVK object conversion are separate source joins.
"""
from . import generate_transfer_ownership_native_endpoint as endpoint


def generate(chunks, selections, ivk_data, ivk_export, reduction_data, reduction_export,
             parameter_root, expected_relation, readonly_lcs=()):
    endpoint.generate(chunks, selections, ivk_data, ivk_export, reduction_data,
        reduction_export, parameter_root, expected_relation, readonly_lcs)
    selected = endpoint.endpoint_plan(chunks, selections)
    cones = endpoint.scalar.native.tables.completion.owner.cone_certificates(chunks[0], selections[0], 0, True)
    formula = next(cone for cone in cones['cones'] if cone['role'] == 'formula0')
    inputs = [cones['observations'][identity][1] for identity in formula['inputs']]
    if len(inputs) != 2 or any(len(lc) != 1 or lc[0][1] != 1 for lc in inputs):
        raise endpoint.owner.relation.RelationError('ownership address exact original diversified singletons')
    bx, by = [lc[0][0] for lc in inputs]
    tx, ty = selected['columns']
    copy = selected['constant_copy']
    name = 'RuntimeOwnershipNativeAddress'
    aliases = dict(E='RuntimeOwnershipNativeEndpoint',N='RuntimeOwnershipNativeConstructor',
        A='ShielddNativeAddress',T='RuntimeOwnershipWindow000NativeTables',
        IV='RuntimeTransferIvkNativeInverseOwned',L='RuntimeTransferOwnership',
        G='RuntimeOwnershipConstructorTrace',D='RuntimeHashBlock_authorization_ivk_0')
    source = '''import ShielddSecurity.RuntimeOwnershipNativeEndpoint
import ShielddSecurity.ShielddNativeAddress
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
''' + f'namespace ShielddSecurity.{name}\n'
    source += ''.join(f'namespace {key} := {value}\n' for key,value in aliases.items())
    source += f'''variable {{F : Type}} [Field F] [CharP F Scalar.modulus]
variable {{Extended Subgroup R K Q Signing J Encoded Native : Type}} [AddCommGroup J]
variable (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
variable (model : Group.StandardCurveModel J (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
variable (upstream : ShielddNativeSdk.Upstream Extended Subgroup R K Q Signing J fq fr
  (RuntimeOwnershipWindow000Point0Cones.coefficientD : F) model)
variable (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
variable (codec : TransferReduction.CanonicalField F) (nk x y : Q) (scalar : R) (base : Nat → F)
variable (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
variable (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
variable (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
variable (primitives : ShielddViewingKeyAdmission.Primitives fq fr)
variable (one : base 0 = 1) (four : (4 : F) ≠ 0) (linked : base {copy} = base 0)
variable (accepted : ShielddViewingKeyAdmission.incomingScalar primitives
  (ShielddNativeIvkSdkProgram.ivk fq arithmetic initial square codec
    (Poseidon.castParameters D.parameters) nk x y) = some scalar)
include arithmetic initial square primitives one linked accepted in
private theorem constructed_coordinates (sender : Subgroup) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    L.base (E.completed fq fr model upstream backend codec nk x y sender scalar base) =
      model.coordinates (upstream.embed (upstream.promote sender)) ∧
    L.target (E.completed fq fr model upstream backend codec nk x y sender scalar base) =
      model.coordinates (fr.integer scalar • upstream.embed (upstream.promote sender)) := by
  let seed := E.seeded fq fr model upstream backend sender scalar base
  let ivk := IV.completeAssignment fq backend codec nk x y seed
  let precomputed := N.precomputed fq fr model upstream backend codec nk x y sender seed
  let built := E.completed fq fr model upstream backend codec nk x y sender scalar base
  have seedOne : seed 0 = 1 := (E.seed_preserves fq fr model upstream backend sender scalar base 0 (by decide)).trans one
  have seedLink : seed {copy} = seed 0 := by
    rw [E.seed_preserves fq fr model upstream backend sender scalar base {copy} (by decide),
      E.seed_preserves fq fr model upstream backend sender scalar base 0 (by decide),linked]
  have ivkOne : ivk 0 = 1 := (N.ivk_constants fq backend codec nk x y seed 0 (by simp)).trans seedOne
  have ivkLink : ivk {copy} = ivk 0 := by
    rw [N.ivk_constants fq backend codec nk x y seed {copy} (by simp),
      N.ivk_constants fq backend codec nk x y seed 0 (by simp),seedLink]
  have windows := N.native_windows_complete fq fr model upstream backend codec nk x y sender scalar seed
    arithmetic initial square primitives seedOne seedLink accepted imaginary nonSquare imaginarySquare
  have kept (column : Nat) (bound : column < 2257) : built column = precomputed column :=
    windows.2.2.2 column (List.mem_append_left _ (List.mem_range.mpr bound))
  have baseStayed : L.base built = L.base precomputed := by
    change Group.Point.mk (eval built [({bx},1)]) (eval built [({by},1)]) =
      Group.Point.mk (eval precomputed [({bx},1)]) (eval precomputed [({by},1)])
    simp only [eval,Int.cast_one,one_mul,add_zero]
    exact congrArg₂ Group.Point.mk (kept {bx} (by decide)) (kept {by} (by decide))
  have baseRead : L.base precomputed = model.coordinates (upstream.embed (upstream.promote sender)) := by
    change GroupFixedCircuitCompletion.point precomputed T.tables.base = _
    exact (T.table_coordinates fq fr model upstream backend sender ivk imaginary nonSquare imaginarySquare ivkOne ivkLink).1
  have targetKept := E.completed_targets fq fr model upstream backend codec nk x y sender scalar base
    arithmetic initial square primitives one linked accepted imaginary nonSquare imaginarySquare
  have targetStayed : L.target built = L.target seed := by
    change Group.Point.mk (eval built [({tx},1)]) (eval built [({ty},1)]) =
      Group.Point.mk (eval seed [({tx},1)]) (eval seed [({ty},1)])
    simp only [eval,Int.cast_one,one_mul,add_zero]
    exact congrArg₂ Group.Point.mk (targetKept {tx} (by decide)) (targetKept {ty} (by decide))
  exact ⟨baseStayed.trans baseRead,targetStayed.trans (E.seeded_target fq fr model upstream backend sender scalar base)⟩
'''
    for mode in ('viewed', 'payment'):
        extra = '[DecidableEq Subgroup] ' if mode == 'viewed' else ''
        params = '''(addressPrimitives : A.Primitives upstream) (address : A.Address Subgroup)'''
        if mode == 'payment':
            params += '\n    (key : A.ShortBytes) (index : A.Index)'
        predicate = ('A.viewsAddress upstream addressPrimitives ⟨fr.bytes scalar⟩ address = true'
            if mode == 'viewed' else
            'A.paymentAddress upstream addressPrimitives ⟨fr.bytes scalar⟩ key index = some address')
        helper = 'viewed_coordinates' if mode == 'viewed' else 'payment_address_coordinates'
        helper_args = 'address' if mode == 'viewed' else 'key index address'
        source += f'''include arithmetic initial square primitives one linked accepted in
theorem {mode}_address_coordinates {extra}{params}
    (legal : {predicate}) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    L.base (E.completed fq fr model upstream backend codec nk x y address.diversified scalar base) =
      model.coordinates (upstream.embed (upstream.promote address.diversified)) ∧
    L.target (E.completed fq fr model upstream backend codec nk x y address.diversified scalar base) =
      model.coordinates (upstream.embed (upstream.promote address.transmission.point)) := by
  have secret := A.secret_from_ivk primitives _ scalar accepted
  have addressValue := A.{helper} upstream addressPrimitives primitives scalar ⟨fr.bytes scalar⟩
    {helper_args} secret legal
  have actual := constructed_coordinates fq fr model upstream backend codec nk x y scalar base
    arithmetic initial square primitives one linked accepted address.diversified imaginary nonSquare imaginarySquare
  exact ⟨actual.1,actual.2.trans addressValue.symm⟩
include arithmetic initial square primitives one four linked accepted in
theorem {mode}_address_complete {extra}{params}
    (legal : {predicate}) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    Satisfies (E.completed fq fr model upstream backend codec nk x y address.diversified scalar base)
      ((RuntimeTransferIvkInversePrefixJoin.originalRows ++ G.originalRows) ++ E.endpointRows) ∧
    L.base (E.completed fq fr model upstream backend codec nk x y address.diversified scalar base) =
      model.coordinates (upstream.embed (upstream.promote address.diversified)) ∧
    L.target (E.completed fq fr model upstream backend codec nk x y address.diversified scalar base) =
      model.coordinates (upstream.embed (upstream.promote address.transmission.point)) := by
  have rows := E.prefix_windows_endpoint_complete fq fr model upstream backend codec nk x y
    address.diversified scalar base arithmetic initial square primitives one four linked accepted
    imaginary nonSquare imaginarySquare
  exact ⟨rows,{mode}_address_coordinates fq fr model upstream backend codec nk x y scalar base
    arithmetic initial square primitives one linked accepted addressPrimitives address ''' + (
        'key index ' if mode == 'payment' else '') + '''legal imaginary nonSquare imaginarySquare⟩
'''
    for name_export in ('viewed_address_coordinates', 'viewed_address_complete',
                        'payment_address_coordinates', 'payment_address_complete'):
        source += '#print axioms ' + name_export + '\n'
    return name,endpoint.scalar.joins._qualify(source+f'end ShielddSecurity.{name}\n',aliases)
