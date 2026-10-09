"""The final statement assertion joins computed output to the distinct claim.

Both genuine source pages are independently reaccepted. No hash computation,
native public encoding or constructed satisfying assignment follows here.
"""
import hashlib
from . import transfer_remaining_pages as pages, transfer_arithmetic as arithmetic
from . import transfer_relation as relation
from .transfer_fixed_spend import canonical, combine


def _selected(manifest_data, role_page, final_page, accepted_roles, parameter_root):
    manifest = pages.inspect_manifest(manifest_data, accepted_roles['metadata']['relation_digest'])
    if manifest['scope'] != 'statement' or len(manifest['pages']) != 14:
        raise relation.RelationError('exact thirteen-block statement scope')
    roles = pages.inspect_page(manifest_data, role_page, 0, accepted_roles)
    final = pages.inspect_page(manifest_data, final_page, 13, accepted_roles, parameter_root)
    if (roles['metadata']['records'] != final['metadata']['records']
            or roles['metadata']['calls'] != final['metadata']['calls']
            or any(roles['metadata'][key] != final['metadata'][key] for key in pages.IDENTITY)):
        raise relation.RelationError('same statement source objects and relation throughout')
    for handle in roles['observed'].keys() & final['observed'].keys():
        if roles['observed'][handle] != final['observed'][handle]:
            raise relation.RelationError('statement cross-page LC alias changed')
    claimed_ref = roles['records']['statement', 'interface', 0][0]
    output_ref = final['metadata']['hash']['output']
    def value(ref, checked):
        kind, handle = pages.reference(ref)
        return canonical([(0, handle)]) if kind == 'native' else checked['observed'][handle]
    claimed, output = value(claimed_ref, roles), value(output_ref, final)
    delta = combine(output, claimed, -1)
    if not delta: raise relation.RelationError('computed statement must not be replaced by claimed LC alias')
    identity = hashlib.sha256(len(role_page).to_bytes(8, 'big') + role_page + len(final_page).to_bytes(8, 'big') + final_page).hexdigest()
    return dict(checked=roles, final=final, claimed=claimed, output=output, delta=delta,
                metadata_sha256=identity, role_page_sha256=hashlib.sha256(role_page).hexdigest(),
                final_page_sha256=hashlib.sha256(final_page).hexdigest())


def extract(manifest_data, role_page, final_page, stream, accepted_roles, parameter_root):
    selected = _selected(manifest_data, role_page, final_page, accepted_roles, parameter_root)
    obj = selected['checked']['metadata']; copy = obj['constant_copy']
    outlined = canonical((copy if column == 0 else column, value) for column, value in selected['delta'])
    required = {(canonical([(0, 1), (copy, -1)]), ()): ['constant-copy'],
                (outlined, ()): ['computed-minus-claimed']}
    extracted = arithmetic.extract_templates(stream, obj['relation_digest'], obj['domain_size'], obj['full_rows'],
                                             required, [], [], label='remaining-statement-final-assertion')
    extracted.update(metadata_sha256=selected['metadata_sha256'], role_page_sha256=selected['role_page_sha256'],
                     final_page_sha256=selected['final_page_sha256'])
    certificates(manifest_data, role_page, final_page, extracted, accepted_roles, parameter_root)
    return extracted


def certificates(manifest_data, role_page, final_page, extracted, accepted_roles, parameter_root):
    selected = _selected(manifest_data, role_page, final_page, accepted_roles, parameter_root)
    if not isinstance(extracted, dict) or any(extracted.get(key) != selected[key] for key in ('role_page_sha256', 'final_page_sha256')):
        raise relation.RelationError('exact both statement pages required')
    raw, rows = arithmetic.normalize_selection(extracted, selected['checked']['metadata'], selected['metadata_sha256'])
    negative = canonical((column, -value) for column, value in selected['delta'])
    matches = [index for index, row in rows.items() if row in ((selected['delta'], ()), (negative, ()))]
    copy = selected['checked']['metadata']['constant_copy']
    links = [index for index, row in raw.items() if row == (canonical([(0, 1), (copy, -1)]), ())]
    if len(matches) != 1 or len(links) != 1 or set(matches + links) != set(raw):
        raise relation.RelationError('exact unique computed-minus-claimed assertion plus constant link')
    selected.update(raw=raw, direct=rows[matches[0]][0] == selected['delta'])
    return selected


def generate(manifest_data, role_page, final_page, extracted, accepted_roles, parameter_root):
    from .generate_hash_round import linear, _signature_audits
    selected = certificates(manifest_data, role_page, final_page, extracted, accepted_roles, parameter_root)
    copy = selected['checked']['metadata']['constant_copy']
    first, second = (selected['output'], selected['claimed']) if selected['direct'] else (selected['claimed'], selected['output'])
    proof = f'Compiler.checked_assertion_sound rho rows {linear(first)} {linear(second)} normalized (by decide)'
    if not selected['direct']: proof = '(' + proof + ').symm'
    source = ('import ShielddSecurity.Compiler\nset_option maxHeartbeats 300000\n'
              'namespace ShielddSecurity.RuntimeTransferStatementBinding\nopen ShielddSecurity\n'
              + f'def modulus : Nat := {relation.MODULUS}\n'
              + 'def originalRows : List Nat := ' + str(sorted(selected['raw'])) + '\n'
              + 'def rawRows : List Row := [' + ',\n'.join('⟨' + linear(a) + ',' + linear(b) + '⟩' for a,b in selected['raw'].values()) + ']\n'
              + f'def rows : List Row := Compiler.unoutlineRows {copy} rawRows\n'
              + f'theorem constantLink : Compiler.checkRow modulus rawRows ⟨[(0,1),({copy},-1)],[]⟩ = true := by decide\n'
              + f'''theorem computed_equals_claimed {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    eval rho {linear(selected['output'])} = eval rho {linear(selected['claimed'])} := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  exact {proof}
#print axioms constantLink
#print axioms computed_equals_claimed
end ShielddSecurity.RuntimeTransferStatementBinding
''')
    return _signature_audits(source)
