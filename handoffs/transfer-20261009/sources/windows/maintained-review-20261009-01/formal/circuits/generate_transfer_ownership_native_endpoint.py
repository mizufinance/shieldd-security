"""Construct exact published transmission assertions from owned native inputs.

Target coordinates are seeded before IVK/precompute/windows and are preserved
by actual write exclusions. Caller/address object association stays separate.
"""
from . import generate_transfer_ownership_native_scalar as scalar
from . import generate_transfer_ownership_native_prefix as prefix
from . import transfer_ownership as owner
from .generate_hash_round import linear


def endpoint_plan(chunks, selections):
    """Select only retained, accepted original endpoint rows; no stream scan."""
    owner.join_chunks(chunks)
    if len(chunks) != 8 or len(selections) != 8:
        raise owner.relation.RelationError('ownership endpoint exact eight accepted chunks')
    try:
        last = chunks[-1]
        observed = lambda role: [last['derived'][value[1]] if value[0] == 'source'
            else owner.canonical([(0, value[1])]) for value in last['points'][role]]
        output, target = observed('output'), observed('target')
        if any(len(terms) != 1 or terms[0][1] != 1 for terms in output + target):
            raise owner.relation.RelationError('ownership endpoint exact actual unit singletons')
        columns = [terms[0][0] for terms in target]
        output_columns = [terms[0][0] for terms in output]
        if len(columns) != 2 or len(output_columns) != 2 or len(set(columns + output_columns)) != 4:
            raise owner.relation.RelationError('ownership endpoint distinct target/output columns')
        raw, roles = {}, {}
        for selected in selections:
            for row in selected['selected_rows']:
                if row['row'] in raw and raw[row['row']] != row:
                    raise owner.relation.RelationError('ownership endpoint overlapping actual rows')
                raw[row['row']] = row
            for entry in selected['templates']:
                for role in entry['roles']:
                    if role.startswith('target.'):
                        if role in roles and roles[role] != entry['row']:
                            raise owner.relation.RelationError('ownership endpoint exact source role row identity')
                        roles[role] = entry['row']
        indices = [roles['target.' + str(axis)] for axis in range(2)]
        if len(set(indices)) != 2:
            raise owner.relation.RelationError('ownership endpoint distinct original rows')
        rows = [tuple(tuple((column, int(value, 16)) for column, value in raw[index][key])
            for key in ('a', 'b')) for index in indices]
        if rows != [(owner.combine(left, right, -1), ()) for left, right in zip(output, target)]:
            raise owner.relation.RelationError('ownership endpoint exact original output-minus-target rows')
        return dict(columns=columns, output_columns=output_columns, indices=indices, rows=rows,
            relation_digest=last['metadata']['relation_digest'], constant_copy=last['metadata']['constant_copy'])
    except (KeyError, TypeError, ValueError, IndexError) as error:
        raise owner.relation.RelationError('ownership endpoint malformed retained metadata') from error


def generate(chunks, selections, ivk_data, ivk_export, reduction_data, reduction_export,
             parameter_root, expected_relation, readonly_lcs=()):
    args = (chunks, selections, ivk_data, ivk_export, reduction_data, reduction_export,
        parameter_root, expected_relation, readonly_lcs)
    scalar.generate(*args)
    prefix.generate(*args)
    selected = endpoint_plan(chunks, selections)
    if selected['relation_digest'] != expected_relation:
        raise owner.relation.RelationError('ownership endpoint same accepted relation')
    accepted = scalar.native.bit_values.bits.consumer.keys.native.hashes.ivk.inspect_metadata(
        ivk_data, parameter_root, expected_relation)
    plan = scalar.native.bit_values.bits.consumer.keys.native.reduction.plan(
        reduction_data, accepted, reduction_export, expected_relation, readonly_lcs)
    q, r = plan['phases'][:2]
    qcol, rcol, qs, rs = q['value'][0][0], r['value'][0][0], q['start'], r['start']
    copy = selected['constant_copy']
    xcol, ycol = selected['columns']
    if any(column == copy or not 0 < column < 2257 or
           qs <= column < qs + q['width'] or rs <= column < rs + r['width'] or
           column in (1980, 1981, 1993, qcol, rcol) for column in selected['columns']):
        raise owner.relation.RelationError('ownership target seed exact shared-role/write separation')
    name = 'RuntimeOwnershipNativeEndpoint'
    aliases = dict(N='RuntimeOwnershipNativeConstructor',P='RuntimeOwnershipNativePrefix',
        NS='RuntimeOwnershipNativeScalar',G='RuntimeOwnershipConstructorTrace',
        F='RuntimeOwnershipWindow000PrecomputeFrame',L='RuntimeTransferOwnership',
        IV='RuntimeTransferIvkNativeInverseOwned',H='RuntimeTransferIvkHashOwnedCompletion',
        I='RuntimeTransferIvkInverseOwnedCompletion',O=scalar.joins.ORDER,S='ShielddViewingKeySeed',
        D='RuntimeHashBlock_authorization_ivk_0')
    source = ''.join(f'import ShielddSecurity.{aliases[key]}\n' for key in ('NS','P','F'))
    source += '''import ShielddSecurity.ScalarReductionFrame
import ShielddSecurity.ShielddNativeOwnershipMultiply
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
''' + f'namespace ShielddSecurity.{name}\n'
    source += ''.join(f'namespace {key} := {value}\n' for key, value in aliases.items())
    source += f'''def targetColumns : List Nat := [{xcol},{ycol}]
def originalEndpointRows : List Nat := {selected['indices']}
def endpointRows : List Row := [
''' + ',\n'.join('  ⟨'+linear(a)+','+linear(b)+'⟩' for a,b in selected['rows']) + ''']
theorem original_endpoint_containment : endpointRows = L.endpointRows := by decide
variable {F : Type} [Field F] [CharP F Scalar.modulus]
variable {E S R K Q Signing J Encoded Native : Type} [AddCommGroup J]
variable (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
variable (model : Group.StandardCurveModel J (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
variable (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr
  (RuntimeOwnershipWindow000Point0Cones.coefficientD : F) model)
variable (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
variable (codec : TransferReduction.CanonicalField F) (nk x y : Q) (sender : S) (scalar : R) (base : Nat → F)
def targetValues : Nat → F := fun column =>
  if column = '''+str(xcol)+''' then S.readValue fq backend
    (upstream.affine (upstream.multiply (upstream.promote sender) scalar)).1
  else if column = '''+str(ycol)+''' then S.readValue fq backend
    (upstream.affine (upstream.multiply (upstream.promote sender) scalar)).2 else 0
def seeded : Nat → F := patchAssignment base
  (targetValues fq fr model upstream backend sender scalar) targetColumns
def completed : Nat → F := N.completed fq fr model upstream backend codec nk x y sender scalar
  (seeded fq fr model upstream backend sender scalar base)
theorem seed_preserves (column : Nat) (outside : column ∉ targetColumns) :
    seeded fq fr model upstream backend sender scalar base column = base column :=
  patchAssignment_preserves base _ _ column outside
theorem seeded_target : L.target (seeded fq fr model upstream backend sender scalar base) =
    model.coordinates (fr.integer scalar • upstream.embed (upstream.promote sender)) := by
  rw [← upstream.multiplyEmbedding,upstream.affineMeaning]
  simp [L.target,seeded,targetValues,targetColumns,patchAssignment,eval,
    S.read_value,ShielddNativeIvkHash.fqValue]
theorem ivk_targets : ∀ column ∈ targetColumns,
    IV.completeAssignment fq backend codec nk x y base column = base column := by
  intro column member
  simp only [targetColumns,List.mem_cons,List.mem_singleton] at member
  rcases member with rfl | rfl
'''
    for column in selected['columns']:
        source += f'''  · let hbase := H.completeAssignment (S.seed fq backend nk x y base)
    let value := eval hbase O.hashValue
    exact (I.preserves _ {column} (by decide)).trans
      ((ScalarReductionFrame.column hbase codec value {qcol} {rcol} {qs} {rs}
        O.allStages {column} (by decide) (by decide) (by decide) (by decide)).trans
        ((H.preserves _ {column} (by decide)).trans
          (S.seed_preserves fq backend nk x y base {column} (by decide))))
'''
    source += f'''variable (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
variable (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
variable (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
variable (primitives : ShielddViewingKeyAdmission.Primitives fq fr)
variable (one : base 0 = 1) (four : (4 : F) ≠ 0) (linked : base {copy} = base 0)
variable (accepted : ShielddViewingKeyAdmission.incomingScalar primitives
  (ShielddNativeIvkSdkProgram.ivk fq arithmetic initial square codec
    (Poseidon.castParameters D.parameters) nk x y) = some scalar)
include arithmetic initial square primitives one linked accepted in
theorem completed_targets (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    ∀ column ∈ targetColumns,
      completed fq fr model upstream backend codec nk x y sender scalar base column =
        seeded fq fr model upstream backend sender scalar base column := by
  let seed := seeded fq fr model upstream backend sender scalar base
  have seedOne : seed 0 = 1 := (seed_preserves fq fr model upstream backend sender scalar base 0 (by decide)).trans one
  have seedLink : seed {copy} = seed 0 := by
    rw [seed_preserves fq fr model upstream backend sender scalar base {copy} (by decide),
      seed_preserves fq fr model upstream backend sender scalar base 0 (by decide),linked]
  have windows := N.native_windows_complete fq fr model upstream backend codec nk x y sender scalar seed
    arithmetic initial square primitives seedOne seedLink accepted imaginary nonSquare imaginarySquare
  intro column member
  have bound : column < 2257 := by
    simp only [targetColumns,List.mem_cons,List.mem_singleton] at member
    rcases member with rfl | rfl <;> decide
  have precomputeOutside : column ∉ F.writes := by
    simp only [targetColumns,List.mem_cons,List.mem_singleton] at member
    rcases member with rfl | rfl <;> decide
  exact (windows.2.2.2 column (List.mem_append_left _ (List.mem_range.mpr bound))).trans
    ((F.outside fq fr model upstream backend sender _ column precomputeOutside).trans
      (ivk_targets fq backend codec nk x y seed column member))
include arithmetic initial square primitives one four linked accepted in
theorem endpoint_rows_complete (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    Satisfies (completed fq fr model upstream backend codec nk x y sender scalar base) endpointRows := by
  let seed := seeded fq fr model upstream backend sender scalar base
  let built := completed fq fr model upstream backend codec nk x y sender scalar base
  have seedOne : seed 0 = 1 := (seed_preserves fq fr model upstream backend sender scalar base 0 (by decide)).trans one
  have seedLink : seed {copy} = seed 0 := by
    rw [seed_preserves fq fr model upstream backend sender scalar base {copy} (by decide),
      seed_preserves fq fr model upstream backend sender scalar base 0 (by decide),linked]
  have value := NS.native_scalar_coordinates fq fr model upstream backend codec nk x y sender scalar seed
    arithmetic initial square primitives seedOne four seedLink accepted imaginary nonSquare imaginarySquare
  have kept := completed_targets fq fr model upstream backend codec nk x y sender scalar base
    arithmetic initial square primitives one linked accepted imaginary nonSquare imaginarySquare
  have target : L.target built = L.target seed := by
    change Group.Point.mk (eval built [({xcol},1)]) (eval built [({ycol},1)]) =
      Group.Point.mk (eval seed [({xcol},1)]) (eval seed [({ycol},1)])
    simp only [eval,Int.cast_one,one_mul,add_zero]
    exact congrArg₂ Group.Point.mk (kept {xcol} (by decide)) (kept {ycol} (by decide))
  have coordinates : RuntimeOwnershipWindow125.result built = L.target built :=
    value.trans ((seeded_target fq fr model upstream backend sender scalar base).symm.trans target.symm)
  have xValue := congrArg Group.Point.x coordinates
  have yValue := congrArg Group.Point.y coordinates
  change eval built [({selected['output_columns'][0]},1)] = eval built [({xcol},1)] at xValue
  change eval built [({selected['output_columns'][1]},1)] = eval built [({ycol},1)] at yValue
  simp only [eval,Int.cast_one,one_mul,add_zero] at xValue yValue
  intro row member
  simp only [endpointRows,List.mem_cons,List.mem_singleton] at member
  rcases member with rfl | rfl
  · simp [Square,eval,xValue]
  · simp [Square,eval,yValue]
include arithmetic initial square primitives one four linked accepted in
theorem prefix_windows_endpoint_complete (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    Satisfies (completed fq fr model upstream backend codec nk x y sender scalar base)
      ((RuntimeTransferIvkInversePrefixJoin.originalRows ++ G.originalRows) ++ endpointRows) := by
  let seed := seeded fq fr model upstream backend sender scalar base
  have seedOne : seed 0 = 1 := (seed_preserves fq fr model upstream backend sender scalar base 0 (by decide)).trans one
  have seedLink : seed {copy} = seed 0 := by
    rw [seed_preserves fq fr model upstream backend sender scalar base {copy} (by decide),
      seed_preserves fq fr model upstream backend sender scalar base 0 (by decide),linked]
  have previous := P.prefix_and_windows_complete fq fr model upstream backend codec nk x y sender scalar seed
    arithmetic initial square primitives seedOne four seedLink accepted imaginary nonSquare imaginarySquare
  have last := endpoint_rows_complete fq fr model upstream backend codec nk x y sender scalar base
    arithmetic initial square primitives one four linked accepted imaginary nonSquare imaginarySquare
  intro row member
  rcases List.mem_append.mp member with prior | endpoint
  · exact previous row prior
  · exact last row endpoint
include arithmetic initial square primitives one four linked accepted in
theorem raw_multiply_endpoint {{Raw : Type}}
    (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (read : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (write : ShielddNativeEncode.Primitives (Encoded := Encoded) operations)
    (standardCoefficient : (RuntimeOwnershipWindow000Point0Cones.coefficientD : F) =
      -(10240 : F) * (10241 : F)⁻¹)
    (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) (two : (2 : F) ≠ 0) :
    (ShielddNativeOwnershipMultiply.multiply operations read write upstream sender scalar).map
      (ShielddNativePoint.pointValue operations) =
    some (RuntimeOwnershipWindow125.result
      (completed fq fr model upstream (ShielddNativeScalar.readerBackend operations read)
        codec nk x y sender scalar base)) := by
  let reader := ShielddNativeScalar.readerBackend operations read
  let seed := seeded fq fr model upstream reader sender scalar base
  have seedOne : seed 0 = 1 := (seed_preserves fq fr model upstream reader sender scalar base 0 (by decide)).trans one
  have seedLink : seed {copy} = seed 0 := by
    rw [seed_preserves fq fr model upstream reader sender scalar base {copy} (by decide),
      seed_preserves fq fr model upstream reader sender scalar base 0 (by decide),linked]
  have value := NS.native_scalar_coordinates fq fr model upstream reader codec nk x y sender scalar seed
    arithmetic initial square primitives seedOne four seedLink accepted imaginary nonSquare imaginarySquare
  exact (ShielddNativeOwnershipMultiply.multiply_coordinates operations read write codec upstream
    standardCoefficient imaginary nonSquare imaginarySquare two sender scalar).trans
    (congrArg some value.symm)
'''
    for export in ('original_endpoint_containment','seed_preserves','seeded_target','ivk_targets',
                   'completed_targets','endpoint_rows_complete','prefix_windows_endpoint_complete','raw_multiply_endpoint'):
        source += '#print axioms ' + export + '\n'
    return name,scalar.joins._qualify(source+f'end ShielddSecurity.{name}\n',aliases)
