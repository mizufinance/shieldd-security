"""Owned SDKProgram Fr scalar to actual ownership accumulator coordinates.

The sender point is seeded by the global owned coordinate reader. The scalar
is the same successful SDKProgram result used by the IVK constructor. Neither
the sender's coordinates nor the final scalar/output equality is a premise.
"""
from . import generate_transfer_ownership_native_constructor as native
from . import generate_transfer_ownership_constructed_scalar as scalar_rows
from . import generate_transfer_ivk_reduction_join as joins


def generate_modules(chunks,selections,ivk_data,ivk_export,reduction_data,reduction_export,
                     parameter_root,expected_relation,readonly_lcs=()):
    """Return the complete ordered endpoint/support inventory after strict joins.

    ``generate`` retains its tuple ABI for the native endpoint. Evidence
    producers use this API so none of its scalar support imports are implicit.
    The pure support render uses the bit-column already accepted by generate.
    """
    name, source = generate(chunks,selections,ivk_data,ivk_export,reduction_data,reduction_export,
                            parameter_root,expected_relation,readonly_lcs)
    bit_start = chunks[0]['derived'][chunks[0]['bits'][0]][0][0]
    emitted = scalar_rows._render_modules(bit_start)
    cones=native.tables.completion.owner.cone_certificates(chunks[0],selections[0],0,True)
    formula=next(cone for cone in cones['cones'] if cone['role']=='formula0')
    xcol,ycol=[cones['observations'][identity][1][0][0] for identity in formula['inputs']]
    emitted.update(_render_modules(chunks[0]['metadata']['constant_copy'],xcol,ycol))
    emitted[name] = source
    return emitted


def generate(chunks,selections,ivk_data,ivk_export,reduction_data,reduction_export,
             parameter_root,expected_relation,readonly_lcs=()):
    native.generate(chunks,selections,ivk_data,ivk_export,reduction_data,reduction_export,
                    parameter_root,expected_relation,readonly_lcs)
    scalar_rows.generate(chunks,selections,readonly_lcs)
    copy=chunks[0]['metadata']['constant_copy']
    cones=native.tables.completion.owner.cone_certificates(chunks[0],selections[0],0,True)
    formula=next(cone for cone in cones['cones'] if cone['role']=='formula0')
    xcol,ycol=[cones['observations'][identity][1][0][0] for identity in formula['inputs']]
    name='RuntimeOwnershipNativeScalar'
    return name,_render_modules(copy,xcol,ycol)[name]


def _render_combined(copy,xcol,ycol):
    """Retain the combined template for strict proof-only correspondence."""
    name='RuntimeOwnershipNativeScalar'
    aliases=dict(N='RuntimeOwnershipNativeConstructor',T='RuntimeOwnershipWindow000NativeTables',
        C='RuntimeOwnershipConstructedScalar',L='RuntimeTransferOwnership',
        IV='RuntimeTransferIvkNativeInverseOwned',G='RuntimeOwnershipConstructorTrace',
        D='RuntimeHashBlock_authorization_ivk_0')
    source=''.join(f'import ShielddSecurity.{aliases[key]}\n' for key in ('N','C'))
    source+='''set_option maxHeartbeats 300000
set_option maxRecDepth 4096
'''+f'namespace ShielddSecurity.{name}\n'
    source+=''.join(f'namespace {key} := {target}\n' for key,target in aliases.items())
    source+=f'''variable {{F : Type}} [Field F] [CharP F Scalar.modulus]
variable {{E S R K Q Signing J Encoded Native : Type}} [AddCommGroup J]
variable (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
variable (model : Group.StandardCurveModel J (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
variable (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr
  (RuntimeOwnershipWindow000Point0Cones.coefficientD : F) model)
variable (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
variable (codec : TransferReduction.CanonicalField F) (nk x y : Q) (sender : S) (scalar : R) (base : Nat → F)
variable (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
variable (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
variable (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
variable (primitives : ShielddViewingKeyAdmission.Primitives fq fr)
variable (one : base 0 = 1) (four : (4 : F) ≠ 0) (linked : base {copy} = base 0)
variable (accepted : ShielddViewingKeyAdmission.incomingScalar primitives
  (ShielddNativeIvkSdkProgram.ivk fq arithmetic initial square codec
    (Poseidon.castParameters D.parameters) nk x y) = some scalar)
include arithmetic initial square primitives one four linked accepted in
theorem native_scalar_coordinates (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    RuntimeOwnershipWindow125.result
      (N.completed fq fr model upstream backend codec nk x y sender scalar base) =
      model.coordinates (fr.integer scalar • upstream.embed (upstream.promote sender)) := by
  let ivk := IV.completeAssignment fq backend codec nk x y base
  let precomputed := N.precomputed fq fr model upstream backend codec nk x y sender base
  let built := N.completed fq fr model upstream backend codec nk x y sender scalar base
  have ivkOne : ivk 0 = 1 := (N.ivk_constants fq backend codec nk x y base 0 (by simp)).trans one
  have ivkLink : ivk {copy} = ivk 0 := by
    rw [N.ivk_constants fq backend codec nk x y base {copy} (by simp),
      N.ivk_constants fq backend codec nk x y base 0 (by simp),linked]
  have windows := N.native_windows_complete fq fr model upstream backend codec nk x y sender scalar base
    arithmetic initial square primitives one linked accepted imaginary nonSquare imaginarySquare
  have kept (column : Nat) (bound : column < 2257) : built column = precomputed column :=
    windows.2.2.2 column (List.mem_append_left _ (List.mem_range.mpr bound))
  have precomputedOne : precomputed 0 = 1 :=
    (T.protected_columns fq fr model upstream backend sender ivk ivkLink 0 (by decide)).trans ivkOne
  have builtOne : built 0 = 1 := (kept 0 (by decide)).trans precomputedOne
  have baseStay : L.base built = L.base precomputed := by
    change Group.Point.mk (eval built [({xcol},1)]) (eval built [({ycol},1)]) =
      Group.Point.mk (eval precomputed [({xcol},1)]) (eval precomputed [({ycol},1)])
    simp only [eval,Int.cast_one,one_mul,add_zero]
    exact congrArg₂ Group.Point.mk (kept {xcol} (by decide)) (kept {ycol} (by decide))
  have baseRead : L.base precomputed = model.coordinates (upstream.embed (upstream.promote sender)) := by
    change GroupFixedCircuitCompletion.point precomputed T.tables.base = _
    exact (T.table_coordinates fq fr model upstream backend sender ivk imaginary nonSquare imaginarySquare ivkOne ivkLink).1
  have bound : fr.integer scalar < 2^252 :=
    lt_trans (fr.bounded scalar) (by decide : Scalar.order < 2^252)
  exact C.scalar_coordinates built (fr.integer scalar) bound builtOne four imaginary model nonSquare imaginarySquare
    (upstream.embed (upstream.promote sender)) (baseStay.trans baseRead) windows.1
    (N.native_bit_values fq fr model upstream backend codec nk x y sender scalar base
      arithmetic initial square primitives one linked accepted)
#print axioms native_scalar_coordinates
'''
    return name,joins._qualify(source+f'end ShielddSecurity.{name}\n',aliases)


def _render_modules(copy,xcol,ycol):
    """Separate native preservation from scalar arithmetic with opaque lemmas.

    The combined public statement is unchanged. Helpers derive every endpoint
    input from the same completed assignment and accepted SDK scalar.
    """
    name,combined=_render_combined(copy,xcol,ycol)
    marker=f'namespace ShielddSecurity.{name}\n'
    imports,content=combined.split(marker,1)
    variables,public=content.split('include arithmetic initial square primitives one four linked accepted in\n',1)
    statement=public.split(' := by\n',1)[0]
    constants='RuntimeOwnershipNativeScalarConstants'
    base='RuntimeOwnershipNativeScalarBase'
    frame='RuntimeOwnershipNativeScalarFrame'
    call='fq fr model upstream backend codec nk x y sender scalar base'
    pre='RuntimeOwnershipNativeConstructor.precomputed fq fr model upstream backend codec nk x y sender base'
    built=f'RuntimeOwnershipNativeConstructor.completed {call}'
    ivk='RuntimeTransferIvkNativeInverseOwned.completeAssignment fq backend codec nk x y base'
    curve='RuntimeOwnershipWindow000Point0Cones.coefficientD'
    imaginary=f'''(imaginary : F)
    (nonSquare : Group.NoUnitSquare ({curve} : F))
    (imaginarySquare : imaginary*imaginary = -1)'''

    def module(namespace,extra,body,names):
        header=imports.replace('import ShielddSecurity.RuntimeOwnershipConstructedScalar\n','')
        position=header.index('set_option maxHeartbeats')
        header=header[:position]+'import ShielddSecurity.RuntimeTransferOwnership\n'+''.join(f'import ShielddSecurity.{item}\n' for item in extra)+header[position:]
        audits=''.join(f'set_option pp.all true in\n#check @{item}\n#print axioms {item}\n' for item in names)
        return header+f'namespace ShielddSecurity.{namespace}\n'+variables+body+audits+f'end ShielddSecurity.{namespace}\n'

    constant_source=f'''include one linked in
theorem ivk_pair : {ivk} 0 = 1 ∧ {ivk} {copy} = {ivk} 0 := by
  have first := RuntimeOwnershipNativeConstructor.ivk_constants fq backend codec nk x y base 0 (by simp)
  have last := RuntimeOwnershipNativeConstructor.ivk_constants fq backend codec nk x y base {copy} (by simp)
  exact ⟨first.trans one,last.trans (linked.trans first.symm)⟩
include one linked in
theorem precomputed_one : {pre} 0 = 1 := by
  let ivk := {ivk}
  have constants := ivk_pair fq backend codec nk x y base one linked
  change RuntimeOwnershipWindow000NativePrecompute.completed fq fr model upstream backend sender ivk 0 = 1
  exact (RuntimeOwnershipWindow000NativeTables.protected_columns fq fr model upstream backend sender ivk constants.2 0 (by decide)).trans constants.1
'''
    base_source=f'''include one linked in
theorem precomputed_base {imaginary} :
    RuntimeTransferOwnership.base ({pre}) = model.coordinates (upstream.embed (upstream.promote sender)) := by
  let ivk := {ivk}
  have constants := {constants}.ivk_pair fq backend codec nk x y base one linked
  change GroupFixedCircuitCompletion.point
    (RuntimeOwnershipWindow000NativePrecompute.completed fq fr model upstream backend sender ivk)
    RuntimeOwnershipWindow000NativeTables.tables.base = _
  exact (RuntimeOwnershipWindow000NativeTables.table_coordinates fq fr model upstream backend sender ivk imaginary nonSquare imaginarySquare constants.1 constants.2).1
'''
    frame_source=f'''include arithmetic initial square primitives one linked accepted in
theorem kept_low {imaginary} (column : Nat) (bound : column < 2257) :
    {built} column = {pre} column := by
  have member : column ∈ RuntimeOwnershipConstructorTrace.kept := by
    change column ∈ List.range 2257 ++ [3766,{copy}]
    exact List.mem_append_left _ (List.mem_range.mpr bound)
  exact (RuntimeOwnershipNativeConstructor.native_windows_complete {call}
    arithmetic initial square primitives one linked accepted imaginary nonSquare imaginarySquare).2.2.2 column member
include arithmetic initial square primitives one linked accepted in
theorem completed_one {imaginary} : {built} 0 = 1 := by
  exact (kept_low {call} arithmetic initial square primitives one linked accepted
    imaginary nonSquare imaginarySquare 0 (by decide)).trans
    ({constants}.precomputed_one fq fr model upstream backend codec nk x y sender base one linked)
include arithmetic initial square primitives one linked accepted in
theorem completed_base {imaginary} :
    RuntimeTransferOwnership.base ({built}) = model.coordinates (upstream.embed (upstream.promote sender)) := by
  have keepX := kept_low {call} arithmetic initial square primitives one linked accepted imaginary nonSquare imaginarySquare {xcol} (by decide)
  have keepY := kept_low {call} arithmetic initial square primitives one linked accepted imaginary nonSquare imaginarySquare {ycol} (by decide)
  have same : RuntimeTransferOwnership.base ({built}) = RuntimeTransferOwnership.base ({pre}) := by
    change Group.Point.mk (eval ({built}) [({xcol},1)]) (eval ({built}) [({ycol},1)]) =
      Group.Point.mk (eval ({pre}) [({xcol},1)]) (eval ({pre}) [({ycol},1)])
    simp only [eval,Int.cast_one,one_mul,add_zero]
    exact congrArg₂ Group.Point.mk keepX keepY
  exact same.trans ({base}.precomputed_base fq fr model upstream backend codec nk x y sender base one linked imaginary nonSquare imaginarySquare)
'''
    body=f'''include arithmetic initial square primitives one four linked accepted in
{statement} := by
  have bound : fr.integer scalar < 2^252 :=
    lt_trans (fr.bounded scalar) (by decide : Scalar.order < 2^252)
  exact RuntimeOwnershipConstructedScalar.scalar_coordinates
    ({built}) (fr.integer scalar) bound
    ({frame}.completed_one {call} arithmetic initial square primitives one linked accepted imaginary nonSquare imaginarySquare)
    four imaginary model nonSquare imaginarySquare (upstream.embed (upstream.promote sender))
    ({frame}.completed_base {call} arithmetic initial square primitives one linked accepted imaginary nonSquare imaginarySquare)
    (RuntimeOwnershipNativeConstructor.native_windows_complete {call}
      arithmetic initial square primitives one linked accepted imaginary nonSquare imaginarySquare).1
    (RuntimeOwnershipNativeConstructor.native_bit_values {call}
      arithmetic initial square primitives one linked accepted)
'''
    return {
        constants:module(constants,[],constant_source,['ivk_pair','precomputed_one']),
        base:module(base,[constants],base_source,['precomputed_base']),
        frame:module(frame,[constants,base],frame_source,['kept_low','completed_one','completed_base']),
        name:module(name,['RuntimeOwnershipConstructedScalar',frame],body,['native_scalar_coordinates']),
    }
