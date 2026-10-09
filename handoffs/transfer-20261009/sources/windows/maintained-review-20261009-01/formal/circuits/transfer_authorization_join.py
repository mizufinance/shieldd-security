"""Maintained same-assignment caller join for the current Transfer relation.

Input acceptance remains the caller-role ingress and accepted component row
extractions. Generated canonical-equality certificates bind each captured LC
to the named component theorem; source handles or digests cannot discharge a
role equality. This is a partial circuit theorem, not native correspondence,
randomizer/RK soundness, completeness, or a Transfer certificate.
"""
from . import transfer_authorization_roles as roles
from . import transfer_relation as relation
from .transfer_balance_rows import canonical, source_index
from .generate_hash_round import linear, _signature_audits

P = relation.MODULUS
FIXED_RING = (
    49822839976625491399435002605169580882773999909559575334089637637825427273330,
    29108985603249989484651727880329493522712908252517904247459350893053326313050,
)
RNK_HASH = canonical([
    (61592, 5579934908212736977238010113730457006906792843192217773053283881663622591681),
    (61596, -1456928232331769666091604024043650394538239072306372778700000267793573709090),
    (61600, -698131897170581497048307930565348753692375937666850051123327179522779327497),
    (61604, 280754542936071555323583947036382301904172335755315562603417507239324752636),
    (61608, -7662113046484220376376826760560917990503811480570254258903603224694465574129),
    (61612, -23883094150264385550751501831181724667314104799878138247322161948146534199289),
])
RNK_COMMITMENT = canonical([
    (61920, 14489116502293865465195620705098702569149962166993518933952339786917836503875),
    (61924, 13125423966940654332711887575940116829944663267413330181877013057693186361539),
    (61928, -14653970678176228351970509534753747945310621286237886970104944815862786477306),
])


def inspect_join(checked, ring_selection, registry_point):
    """Check actual caller LCs against the accepted current component roles.

    ``checked`` is the output of transfer_authorization_roles.inspect_metadata,
    after its accepted RNK/IVK joins. ``ring_selection`` is the accepted output
    of extract_ring_selection. ``registry_point`` is the accepted cofactor
    extraction's two integer LCs (its ``point`` field). The caller must retain
    acceptance receipts for these inputs; this function does not create them.
    The generated theorem also checks equality to the imported Lean modules.
    """
    if not isinstance(checked, dict) or not isinstance(checked.get('metadata'), dict):
        raise relation.RelationError('accepted caller-role parser output required')
    obj = checked['metadata']
    observed = roles._expressions(obj.get('expressions'), obj['domain_size'],
                                  obj['constant_copy'], 512, 'caller join')
    if observed != checked.get('observed'):
        raise relation.RelationError('caller join parser expression mismatch')
    identity = ring_selection.get('identity', {}) if isinstance(ring_selection, dict) else {}
    if (identity.get('relation_digest') != obj['relation_digest'] or
            relation.natural(identity.get('domain_size')) != obj['domain_size'] or
            relation.natural(identity.get('stored_rows')) != obj['full_rows']):
        raise relation.RelationError('accepted ring extraction identity mismatch')
    leaf_columns = ring_selection.get('leaf_columns')
    if (not isinstance(leaf_columns, list) or len(leaf_columns) != 2 or
            [relation.natural(c, obj['domain_size']) for c in leaf_columns] != [23, 24] or
            ring_selection.get('fixed_coordinates') != list(FIXED_RING)):
        raise relation.RelationError('accepted ring extraction/current module role mismatch')
    if not isinstance(registry_point, (list, tuple)) or len(registry_point) != 2:
        raise relation.RelationError('accepted registry point/current module role mismatch')
    registry = []
    for axis in registry_point:
        if not isinstance(axis, (list, tuple)) or len(axis) != 1:
            raise relation.RelationError('accepted registry point/current module role mismatch')
        terms = []
        for term in axis:
            if not isinstance(term, (list, tuple)) or len(term) != 2:
                raise relation.RelationError('accepted registry point/current module role mismatch')
            column = relation.natural(term[0], obj['domain_size'])
            value = term[1]
            if isinstance(value, bool) or not isinstance(value, int) or not 0 < value < P:
                raise relation.RelationError('noncanonical registry point coefficient')
            terms.append((column, value))
        registry.append(tuple(terms))
    if tuple(registry) != (((23, 1),), ((24, 1),)):
        raise relation.RelationError('accepted registry point/current module role mismatch')
    caller, bindings = obj['caller'], obj['rnk_bindings']

    def lc(value):
        return observed[source_index(value['source'])]

    values = {name: lc(caller[name]) for name in
              ('regulated', 'asset', 'nk', 'effective_nk', 'registered_rnk')}
    for name in ('ak', 'address', 'rnk_dh', 'selected_ring', 'leaf_ring'):
        for index, value in enumerate(caller[name]):
            values[name + str(index)] = lc(value)
    for index, value in enumerate(caller['fixed_ring']):
        values['fixed_ring' + str(index)] = canonical([(0, int(value['native'], 16))])
    expected = dict(regulated=((10, 1),), asset=((6, 1),), nk=((1993, 1),),
                    effective_nk=((1993, 1), (61932, 1)), registered_rnk=((1528, 1),),
                    ak0=((1980, 1),), ak1=((1981, 1),),
                    address0=((1504, 1),), address1=((1505, 1),),
                    address2=((1512, 1),), address3=((1513, 1),),
                    rnk_dh0=((1520, 1),), rnk_dh1=((1521, 1),),
                    leaf_ring0=((23, 1),), leaf_ring1=((24, 1),),
                    fixed_ring0=((0, FIXED_RING[0]),), fixed_ring1=((0, FIXED_RING[1]),),
                    selected_ring0=canonical([(0, FIXED_RING[0]), (33796, 1)]),
                    selected_ring1=canonical([(0, FIXED_RING[1]), (33798, 1)]))
    for name, value in expected.items():
        if values[name] != value:
            raise relation.RelationError('caller join current component LC mismatch: ' + name)
    # Hash/output roles were compared with accepted RNK metadata by the ingress;
    # the generated module repeats the exact LC equality against its imports.
    for name in ('hash', 'commitment'):
        values[name] = lc(bindings[name])
    if values['hash'] != RNK_HASH or values['commitment'] != RNK_COMMITMENT:
        raise relation.RelationError('caller join current hash/commitment LC mismatch')
    return dict(metadata=obj, values=values)


def generate_caller_join(checked, ring_selection, registry_point):
    """Generate role certificates and a common-assignment circuit composition."""
    state = inspect_join(checked, ring_selection, registry_point)
    values = state['values']
    source = '''import ShielddSecurity.RuntimeTransferOwnershipIvk
import ShielddSecurity.RuntimeTransferAuthorizationAk
import ShielddSecurity.RuntimeRnkPoints
import ShielddSecurity.RuntimeTransferAssetNonzero
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace ShielddSecurity.RuntimeTransferAuthorizationCaller
def modulus : Nat := RuntimeTransferOwnership.modulus
-- Captured caller boundaries only. Native interpretations and randomizer/RK remain open.
'''
    source += '-- Actual ordinary relation: ' + state['metadata']['relation_digest'] + '\n'
    for name, value in values.items():
        source += 'def ' + name + ' : Linear := ' + linear(value) + '\n'
    for name, x, y in (
            ('akPoint', 'ak0', 'ak1'), ('diversified', 'address0', 'address1'),
            ('transmission', 'address2', 'address3'), ('dhBase', 'rnk_dh0', 'rnk_dh1'),
            ('selectedRing', 'selected_ring0', 'selected_ring1'),
            ('leafRing', 'leaf_ring0', 'leaf_ring1'), ('fixedRing', 'fixed_ring0', 'fixed_ring1')):
        source += f'''def {name} {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F :=
  ⟨eval rho {x},eval rho {y}⟩
'''
    scalar_targets = dict(regulated='RuntimeRnkSelection.regulated', asset='RuntimeTransferAssetNonzero.asset',
                          nk='RuntimeRnkSelection.nk', effective_nk='RuntimeRnkSelection.effective',
                          registered_rnk='RuntimeRnkSelection.registered',
                          hash='RuntimeRnkSponge.output', commitment='RuntimeRnkSponge.commitment')
    for name, target in scalar_targets.items():
        source += f'''theorem {name}_role {{F : Type}} [Field F] [CharP F modulus] (rho : Nat → F) :
    eval rho {name} = eval rho {target} :=
  Compiler.canonical_equal rho {name} {target} (by decide)
'''
    point_targets = dict(akPoint='RuntimeTransferAk.point', diversified='RuntimeTransferOwnership.base',
                         transmission='RuntimeTransferOwnership.target', dhBase='RuntimeTransferRnkLoop.base',
                         selectedRing='RuntimeSelectedRing.selected', leafRing='RuntimeRegistryRing.point',
                         fixedRing='RuntimeSelectedRing.fixed')
    for name, target in point_targets.items():
        source += f'''theorem {name}_role {{F : Type}} [Field F] [CharP F modulus] (rho : Nat → F) :
    {name} rho = {target} rho := by
  apply congrArg₂ Group.Point.mk
  · exact Compiler.canonical_equal rho _ _ (by decide)
  · exact Compiler.canonical_equal rho _ _ (by decide)
'''
    source += '''theorem ivk_inputs_role {F : Type} [Field F] [CharP F modulus] (rho : Nat → F) :
    RuntimeHashBlock_authorization_ivk_0.callInputs.map (eval rho) =
      [eval rho nk,(akPoint rho).x,(akPoint rho).y] := by
  rw [RuntimeTransferAuthorization.input_columns]
  exact congrArg (fun (inputs : List Linear) => inputs.map (eval rho))
    (show RuntimeHashBlock_authorization_ivk_0.callInputs = [nk,ak0,ak1] from rfl)

theorem middle_inputs_role {F : Type} [Field F] [CharP F modulus] (rho : Nat → F) :
    RuntimeRnkPoints.middleInputs.map (eval rho) =
      [(diversified rho).x,(diversified rho).y,
       (transmission rho).x,(transmission rho).y,eval rho asset] := by rfl

def rawRows : List Row := RuntimeTransferOwnershipIvk.rawRows ++
  (RuntimeRnkPoints.rawRows ++ (RuntimeTransferAk.rawRows ++ RuntimeTransferAssetNonzero.rawRows))

theorem reduced_scalar_unique {F : Type} [Field F] [CharP F modulus]
    (q r q' r' : Nat) (rBound : r < Scalar.order) (rBound' : r' < Scalar.order)
    (noWrap : q * Scalar.order + r < Scalar.modulus)
    (noWrap' : q' * Scalar.order + r' < Scalar.modulus)
    (equal : ((q * Scalar.order + r : Nat) : F) = ((q' * Scalar.order + r' : Nat) : F)) :
    r = r' := by
  have natural := bounded_cast_injective (F := F) (p := Scalar.modulus) noWrap noWrap' equal
  have remainder := congrArg (fun value => value % Scalar.order) natural
  simpa only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,mul_zero,Nat.zero_mod,zero_add,
    Nat.mod_eq_of_lt rBound,Nat.mod_eq_of_lt rBound'] using remainder

theorem actual_caller {F J : Type} [Field F] [CharP F modulus] [AddCommGroup J]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (codec : TransferReduction.CanonicalField F)
    (model : Group.StandardCurveModel J (RuntimeTransferOwnership.coefficientD : F))
    (standardOrder : ∀ represented : J, (8 * RuntimeTransferAk.subgroupOrder) • represented = 0)
    (satisfied : Satisfies rho rawRows) :
    ∃ q r : Nat, ∃ ownerBase dhPoint ringPoint actionKey : J,
      q ≤ 8 ∧ 0 < r ∧ r < Scalar.order ∧ q * Scalar.order + r < Scalar.modulus ∧
      ((q * Scalar.order + r : Nat) : F) =
        Poseidon.hash6 (Poseidon.castParameters RuntimeHashBlock_authorization_ivk_0.parameters) 16
          [eval rho nk,(akPoint rho).x,(akPoint rho).y] ∧
      model.coordinates ownerBase = diversified rho ∧
      RuntimeTransferAk.subgroupOrder • ownerBase = 0 ∧ ownerBase ≠ 0 ∧
      transmission rho = model.coordinates (r • ownerBase) ∧
      model.coordinates dhPoint = dhBase rho ∧
      RuntimeTransferAk.subgroupOrder • dhPoint = 0 ∧ dhPoint ≠ 0 ∧
      RuntimeRnkTrace112.window13_output rho = model.coordinates (r • dhPoint) ∧
      RuntimeRnkTrace112.window13_output rho ≠ Group.identityPoint ∧
      model.coordinates ringPoint = selectedRing rho ∧
      RuntimeTransferCofactor.subgroupOrder • ringPoint = 0 ∧ ringPoint ≠ 0 ∧
      model.coordinates actionKey = akPoint rho ∧
      RuntimeTransferAk.subgroupOrder • actionKey = 0 ∧ actionKey ≠ 0 ∧
      eval rho asset ≠ 0 ∧
      eval rho hash =
        Poseidon.hash6 (Poseidon.castParameters RuntimeHashBlock_authorization_rnk_permutation0_0.parameters) 17
          ([(model.coordinates (r • dhPoint)).x,(model.coordinates (r • dhPoint)).y] ++
           [(diversified rho).x,(diversified rho).y,(transmission rho).x,(transmission rho).y,
            eval rho asset,(model.coordinates ringPoint).x,(model.coordinates ringPoint).y]) ∧
      eval rho commitment =
        Poseidon.hash3 (Poseidon.castParameters RuntimeHashBlock_authorization_rnk_permutation2_0.parameters)
          18 [eval rho hash] ∧
      ((eval rho regulated = 0 ∧ eval rho effective_nk = eval rho nk) ∨
       (eval rho regulated = 1 ∧ eval rho commitment = eval rho registered_rnk ∧
        eval rho effective_nk = eval rho hash)) := by
  have ownerSat : Satisfies rho RuntimeTransferOwnershipIvk.rawRows := by
    intro row member; exact satisfied row (List.mem_append.mpr (Or.inl member))
  have rnkSat : Satisfies rho RuntimeRnkPoints.rawRows := by
    intro row member; exact satisfied row (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl member))))
  have akSat : Satisfies rho RuntimeTransferAk.rawRows := by
    intro row member; exact satisfied row (List.mem_append.mpr (Or.inr
      (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl member))))))
  have assetSat : Satisfies rho RuntimeTransferAssetNonzero.rawRows := by
    intro row member; exact satisfied row (List.mem_append.mpr (Or.inr
      (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr member))))))
  obtain ⟨q,r,ownerBase,qBound,positive,rBound,noWrap,ivkHash,ownerRole,ownerSubgroup,ownerNonzero,ownerTarget⟩ :=
    RuntimeTransferOwnershipIvk.actual_ivk_ownership rho one four codec model standardOrder ownerSat
  obtain ⟨q',r',dhPoint,ringPoint,qBound',positive',rBound',noWrap',ivkHash',dhRole,dhSubgroup,
    dhNonzero,dhOutput,rnkHash,rnkCommitment,branches,ringRole,ringSubgroup,ringNonzero⟩ :=
    RuntimeRnkPoints.actual_rnk_points rho one four codec model standardOrder rnkSat
  have same := reduced_scalar_unique (F := F) q r q' r' rBound rBound' noWrap noWrap'
    (ivkHash.trans ivkHash'.symm)
  subst r'
  have joinedSat : Satisfies rho RuntimeRnkJoined.rawRows := by
    intro row member; exact rnkSat row (List.mem_append.mpr (Or.inl member))
  have dhNonidentity := RuntimeRnkJoined.actual_dh_nonidentity rho one four joinedSat
  obtain ⟨actionKey,akRole,akSubgroup,akNonzero⟩ :=
    RuntimeTransferAk.actual_ak_subgroup model standardOrder rho one akSat
  have assetNonzero := RuntimeTransferAssetNonzero.asset_nonzero rho one four assetSat
  rw [← diversified_role rho] at ownerRole
  rw [← transmission_role rho] at ownerTarget
  rw [← dhBase_role rho] at dhRole
  rw [← selectedRing_role rho] at ringRole
  rw [← akPoint_role rho] at akRole
  rw [ivk_inputs_role rho] at ivkHash
  rw [middle_inputs_role rho] at rnkHash
  rw [← hash_role rho] at rnkHash rnkCommitment branches
  rw [← commitment_role rho] at rnkCommitment branches
  rw [← regulated_role rho,← effective_nk_role rho,← nk_role rho,← registered_rnk_role rho] at branches
  rw [← asset_role rho] at assetNonzero
  exact ⟨q,r,ownerBase,dhPoint,ringPoint,actionKey,qBound,positive,rBound,noWrap,ivkHash,
    ownerRole,ownerSubgroup,ownerNonzero,ownerTarget,dhRole,dhSubgroup,dhNonzero,dhOutput,
    dhNonidentity,ringRole,ringSubgroup,ringNonzero,akRole,akSubgroup,akNonzero,
    assetNonzero,rnkHash,rnkCommitment,branches⟩

theorem caller_registry_subgroup {F J : Type} [Field F] [CharP F modulus] [AddCommGroup J]
    (rho : Nat → F) (one : rho 0 = 1)
    (model : Group.StandardCurveModel J (RuntimeTransferOwnership.coefficientD : F))
    (standardOrder : ∀ represented : J, (8 * RuntimeTransferAk.subgroupOrder) • represented = 0)
    (satisfied : Satisfies rho rawRows) :
    ∃ leaf : J, model.coordinates leaf = leafRing rho ∧ RuntimeTransferCofactor.subgroupOrder • leaf = 0 := by
  have registrySat : Satisfies rho RuntimeRegistryRing.rawRows := by
    intro row member
    exact satisfied row (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl
      (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl member))))))))
  obtain ⟨leaf,coordinates,subgroup⟩ := RuntimeRegistryRing.actual_subgroup model standardOrder rho one registrySat
  rw [← leafRing_role rho] at coordinates
  exact ⟨leaf,coordinates,subgroup⟩
end ShielddSecurity.RuntimeTransferAuthorizationCaller
'''
    exports = ([name + '_role' for name in scalar_targets] +
               [name + '_role' for name in point_targets] +
               ['ivk_inputs_role', 'middle_inputs_role', 'reduced_scalar_unique',
                'actual_caller', 'caller_registry_subgroup'])
    audits = ''.join('#print axioms ' + name + '\n' for name in exports)
    source = source.replace('end ShielddSecurity.RuntimeTransferAuthorizationCaller\n',
                            audits + 'end ShielddSecurity.RuntimeTransferAuthorizationCaller\n')
    return _signature_audits(source)
