"""Join constrained leaf cofactors and regulated selectors to represented keys.

Native fallback representation/subgroup facts are explicit parameter contracts.
Leaf membership and both selected coordinates are conclusions from actual rows;
caller labels, native constant decoding, and full-matrix coverage stay separate.
"""
from . import transfer_relation as relation
from .transfer_encryption_dh_keys import infer_regulated_selectors
from .transfer_balance_rows import canonical
from .generate_hash_round import linear, _signature_audits


def generate(checked, cofactors):
    metadata = checked.get('metadata', {})
    if (checked.get('qualified') is not True or
            metadata.get('schema') != 'shieldd-transfer-encryption-dh-v1' or
            type(metadata.get('role')) is not int or metadata['role'] != 0):
        raise relation.RelationError('DH key meaning qualified first occurrence required')
    inferred = infer_regulated_selectors(checked)
    if cofactors.get('selectors') != inferred:
        raise relation.RelationError('DH key meaning same inferred key selector source required')
    items = cofactors.get('cofactors', [])
    names = ['RuntimeTransferEncryptionLeafDetectionSubgroup', 'RuntimeTransferEncryptionLeafPayloadSubgroup']
    if len(items) != 2 or [item.get('namespace') for item in items] != names:
        raise relation.RelationError('DH key meaning both exact leaf cofactor modules required')
    def actual(value):
        if value[0] != 'source':
            return canonical([(0, value[1])])
        if value[1] not in checked['derived']:
            raise relation.RelationError('DH key meaning missing captured source LC')
        return checked['derived'][value[1]]
    flag = actual(inferred['regulated_candidate'])
    points = {}
    for key, label, item in zip(('detection_key', 'payload_key'), ('Detection', 'Payload'), items):
        selected = inferred['selectors'][key]
        leaf = tuple(map(actual, selected['leaf']))
        point = tuple(tuple((int(c), int(v)) for c, v in terms) for terms in item.get('point', ()))
        if point != leaf:
            raise relation.RelationError('DH key meaning exact constrained leaf point LC required')
        if actual(selected['flag']) != flag:
            raise relation.RelationError('DH key meaning common regulated flag LC required')
        points[label] = dict(leaf=leaf, native=tuple(map(actual, selected['fallback'])),
                             selected=tuple(map(actual, selected['output'])))
    name = 'RuntimeTransferEncryptionKeyMeaning'
    regulated = 'RuntimeTransferEncryptionRegulatedFlag'
    output = ['import ShielddSecurity.RuntimeTransferEncryptionRegulatedFlag\n']
    output.extend(f'import ShielddSecurity.RuntimeTransferEncryption{label}KeySelection\n'
                  f'import ShielddSecurity.RuntimeTransferEncryptionLeaf{label}Subgroup\n'
                  for label in ('Detection', 'Payload'))
    output.append(f'namespace ShielddSecurity.{name}\nset_option maxHeartbeats 400000\n')
    output.append(f'def flag : Linear := {linear(flag)}\n')
    for label, values in points.items():
        for role in ('leaf', 'native', 'selected'):
            x, y = values[role]
            output.append(f'def {role}{label} {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F :=\n'
                          f'  ⟨eval rho {linear(x)}, eval rho {linear(y)}⟩\n')
        output.append(f'theorem leaf{label}_role {{F : Type}} [Field F] (rho : Nat → F) :\n'
                      f'    RuntimeTransferEncryptionLeaf{label}Subgroup.point rho = leaf{label} rho := rfl\n')
    output.append(f'theorem flag_role : {regulated}.flag = flag := by decide\n')
    output.append('def rows : List Row := ' + regulated + '.rawRows ++ (\n'
                  '  RuntimeTransferEncryptionDetectionKeySelection.rawRows ++ (\n'
                  '  RuntimeTransferEncryptionPayloadKeySelection.rawRows ++ (\n'
                  '  RuntimeTransferEncryptionLeafDetectionSubgroup.rawRows ++\n'
                  '  RuntimeTransferEncryptionLeafPayloadSubgroup.rawRows)))\n')
    providers = [regulated, 'RuntimeTransferEncryptionDetectionKeySelection',
                 'RuntimeTransferEncryptionPayloadKeySelection',
                 'RuntimeTransferEncryptionLeafDetectionSubgroup',
                 'RuntimeTransferEncryptionLeafPayloadSubgroup']
    output.append('private theorem row_parts {F : Type} [Field F] (rho : Nat → F)\n'
                  '    (satisfied : Satisfies rho rows) :\n    ' +
                  ' ∧\n    '.join('Satisfies rho ' + provider + '.rawRows' for provider in providers) +
                  ' := by\n  refine ⟨?_, ?_, ?_, ?_, ?_⟩\n')
    for index in range(5):
        member = 'member' if index == 4 else 'Or.inl member'
        member = 'Or.inr (' * index + member + ')' * index
        output.append('  · intro row member\n    apply satisfied row\n'
                      '    simp only [rows, List.mem_append]\n'
                      f'    exact {member}\n')
    common = ('{F : Type} [Field F] [CharP F RuntimeTransferCofactorCones.modulus]\n'
              '    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)\n'
              '    (satisfied : Satisfies rho rows)')
    output.append(f'theorem flag_boolean {common} : eval rho flag = 0 ∨ eval rho flag = 1 := by\n'
                  '  have parts := row_parts rho satisfied\n'
                  f'  have result := {regulated}.flag_boolean rho one four parts.1\n'
                  '  rw [flag_role] at result\n  exact result\n')
    for label in ('Detection', 'Payload'):
        module = f'RuntimeTransferEncryption{label}KeySelection'
        satisfaction = 'parts.2.1' if label == 'Detection' else 'parts.2.2.1'
        output.append(f'theorem selected{label}_interpolation {common} :\n'
                      f'    selected{label} rho = EncryptionDhSelection.select (eval rho flag)\n'
                      f'      (leaf{label} rho) (native{label} rho) := by\n'
                      '  have parts := row_parts rho satisfied\n'
                      '  apply congrArg₂ Group.Point.mk\n')
        for axis, coordinate in ((0, 'X'), (1, 'Y')):
            output.append(f'  · change eval rho {module}.out{axis} = eval rho {module}.no{coordinate} +\n'
                          f'      eval rho {module}.flag * (eval rho {module}.yes{coordinate} - eval rho {module}.no{coordinate})\n'
                          f'    exact {module}.axis{axis}_interpolation rho one four {satisfaction}\n')
    output.append(f'''theorem represented_keys {{F J : Type}} [Field F] [DecidableEq F]
    [CharP F RuntimeTransferCofactorCones.modulus] [AddCommGroup J]
    (model : Group.StandardCurveModel J (RuntimeTransferCofactorCones.coefficientD : F))
    (standardOrder : ∀ point : J, (8 * RuntimeTransferCofactor.subgroupOrder) • point = 0)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (fallbackDetection fallbackPayload : J)
    (detectionRole : model.coordinates fallbackDetection = nativeDetection rho)
    (payloadRole : model.coordinates fallbackPayload = nativePayload rho)
    (detectionOrder : RuntimeTransferCofactor.subgroupOrder • fallbackDetection = 0)
    (payloadOrder : RuntimeTransferCofactor.subgroupOrder • fallbackPayload = 0)
    (satisfied : Satisfies rho rows) :
    ∃ leafD leafP selectedD selectedP : J,
      model.coordinates leafD = leafDetection rho ∧
      RuntimeTransferCofactor.subgroupOrder • leafD = 0 ∧
      model.coordinates leafP = leafPayload rho ∧
      RuntimeTransferCofactor.subgroupOrder • leafP = 0 ∧
      selectedD = (if eval rho flag = 1 then leafD else fallbackDetection) ∧
      selectedP = (if eval rho flag = 1 then leafP else fallbackPayload) ∧
      model.coordinates selectedD = selectedDetection rho ∧
      RuntimeTransferCofactor.subgroupOrder • selectedD = 0 ∧
      model.coordinates selectedP = selectedPayload rho ∧
      RuntimeTransferCofactor.subgroupOrder • selectedP = 0 := by
  have parts := row_parts rho satisfied
  obtain ⟨leafD, coordinatesD, orderD⟩ :=
    RuntimeTransferEncryptionLeafDetectionSubgroup.actual_subgroup model standardOrder rho one parts.2.2.2.1
  obtain ⟨leafP, coordinatesP, orderP⟩ :=
    RuntimeTransferEncryptionLeafPayloadSubgroup.actual_subgroup model standardOrder rho one parts.2.2.2.2
  rw [leafDetection_role rho] at coordinatesD
  rw [leafPayload_role rho] at coordinatesP
  have boolean := flag_boolean rho one four satisfied
  let selectedD := if eval rho flag = 1 then leafD else fallbackDetection
  let selectedP := if eval rho flag = 1 then leafP else fallbackPayload
  have meaningD : model.coordinates selectedD = selectedDetection rho := by
    calc
      _ = EncryptionDhSelection.select (eval rho flag) (model.coordinates leafD)
            (model.coordinates fallbackDetection) :=
        (EncryptionDhSelection.represented_selection model (eval rho flag) leafD fallbackDetection boolean).symm
      _ = EncryptionDhSelection.select (eval rho flag) (leafDetection rho) (nativeDetection rho) := by
        rw [coordinatesD, detectionRole]
      _ = selectedDetection rho := (selectedDetection_interpolation rho one four satisfied).symm
  have meaningP : model.coordinates selectedP = selectedPayload rho := by
    calc
      _ = EncryptionDhSelection.select (eval rho flag) (model.coordinates leafP)
            (model.coordinates fallbackPayload) :=
        (EncryptionDhSelection.represented_selection model (eval rho flag) leafP fallbackPayload boolean).symm
      _ = EncryptionDhSelection.select (eval rho flag) (leafPayload rho) (nativePayload rho) := by
        rw [coordinatesP, payloadRole]
      _ = selectedPayload rho := (selectedPayload_interpolation rho one four satisfied).symm
  have selectedOrderD : RuntimeTransferCofactor.subgroupOrder • selectedD = 0 := by
    by_cases branch : eval rho flag = 1 <;> simp only [selectedD, branch, if_true, if_false] <;> assumption
  have selectedOrderP : RuntimeTransferCofactor.subgroupOrder • selectedP = 0 := by
    by_cases branch : eval rho flag = 1 <;> simp only [selectedP, branch, if_true, if_false] <;> assumption
  exact ⟨leafD, leafP, selectedD, selectedP, coordinatesD, orderD, coordinatesP, orderP,
    rfl, rfl, meaningD, selectedOrderD, meaningP, selectedOrderP⟩
''')
    exports = ['leafDetection_role', 'leafPayload_role', 'flag_role', 'flag_boolean',
               'selectedDetection_interpolation', 'selectedPayload_interpolation', 'represented_keys']
    output.extend(f'#print axioms {theorem}\n' for theorem in exports)
    output.append(f'end ShielddSecurity.{name}\n')
    return name, _signature_audits(''.join(output))
