"""Join two inferred DH leaf operands to complete actual cofactor rows.

Column maps are search candidates only. The existing owned71-row matcher and
generated cofactor kernel checks must establish every mapped row. Native and
caller/parameter associations are separate; identity is allowed for leaf keys.
"""
from . import transfer_relation as relation
from .transfer_encryption_dh_keys import infer_regulated_selectors
from .transfer_ownership import extract_cofactor_substitutions, generate_cofactor_substitution


def extract(checked, template, candidate_columns, stream):
    selectors = infer_regulated_selectors(checked)
    metadata = checked['metadata']
    keys = ('detection_key', 'payload_key')
    if not isinstance(candidate_columns, dict) or set(candidate_columns) != set(keys):
        raise relation.RelationError('DH exactly two cofactor column candidates required')
    identity = template.get('identity', {})
    if any(identity.get(a) != metadata[b] for a, b in
           [('relation_digest', 'relation_digest'), ('domain_size', 'domain_size'), ('stored_rows', 'full_rows')]):
        raise relation.RelationError('DH cofactor exact template/occurrence relation identity required')
    requests = []
    for key, label in zip(keys, ('Detection', 'Payload')):
        point = []
        for value in selectors['selectors'][key]['leaf']:
            if value[0] != 'source' or value[1][0] != 1:
                raise relation.RelationError('DH cofactor leaf must retain witness source roles')
            terms = checked['derived'][value[1]]
            if terms != ((value[1][1] + 3, 1),):
                raise relation.RelationError('DH cofactor leaf source/LC identity required')
            point.append(terms)
        requests.append(dict(namespace=f'RuntimeTransferEncryptionLeaf{label}Subgroup',
                             columns=candidate_columns[key], point=tuple(point)))
    actual = extract_cofactor_substitutions(template, requests, stream,
                                           metadata['relation_digest'], cofactor_only=True)
    return dict(selectors=selectors, cofactors=actual,
                scope='Both DH leaf source coordinates and complete71-row cofactor transports; generated kernels/native/caller/parameter roles OPEN')


def generate(extracted):
    cofactors = extracted.get('cofactors')
    expected = ['RuntimeTransferEncryptionLeafDetectionSubgroup', 'RuntimeTransferEncryptionLeafPayloadSubgroup']
    if not isinstance(cofactors, list) or len(cofactors) != 2 or [item['namespace'] for item in cofactors] != expected:
        raise relation.RelationError('DH exact detection/payload cofactor transport modules required')
    return [(item['namespace'], generate_cofactor_substitution(item, cofactor_only=True)) for item in cofactors]
