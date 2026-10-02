"""Bind the closed Rust projection extract to the independent semantic record.

The role mapping below is reviewed specification, not inferred from the order
being checked. The Rust AST interpreter remains an explicit translation TCB.
Canonical decoding and cryptographic statement binding are separate obligations.
"""


def roles():
    pairs = [
        ('rk.x', 'rkX'), ('rk.y', 'rkY'), ('anchor', 'anchor'),
        ('outputs[0].note', 'recipientNote'), ('outputs[0].recovery', 'recipientRecovery'),
        ('outputs[1].note', 'changeNote'), ('outputs[1].recovery', 'changeRecovery'),
        ('balance.x', 'balanceX'), ('balance.y', 'balanceY'),
        ('routing_tags[0]', 'recipientRouting'), ('routing_tags[1]', 'changeRouting'),
        ('routing_parameter', 'routingParameters'),
        ('volume.nullifier', 'volumeNullifier'), ('volume.commitment', 'volumeCommitment'),
        ('volume.day_start', 'volumeDayStart'), ('volume.context', 'volumeContext'),
        ('spends[0].nullifier', 'firstNullifier'),
        ('spends[1].nullifier', 'secondNullifier'),
        ('asset_anchor', 'assetRoot'), ('compliance_anchor', 'userRoot'),
    ]
    pairs += [(f'audit.detection[{i}]', f'detection{i}') for i in range(4)]
    for source, semantic in [('sender', 'sender'), ('output', 'output')]:
        pairs += [(f'audit.{source}_core.{field}', f'{semantic}Core{name}')
                  for field, name in [('epk.x', 'EpkX'), ('epk.y', 'EpkY'),
                                      ('c2', 'C2'), ('ciphertext', 'Ciphertext')]]
        pairs += [(f'audit.{source}_ext.{field}', f'{semantic}Ext{name}')
                  for field, name in [('epk.x', 'EpkX'), ('epk.y', 'EpkY'), ('c2', 'C2')]]
        pairs += [(f'audit.{source}_ext.ciphertext[{i}]', f'{semantic}ExtCiphertext{i}') for i in range(3)]
    pairs += [
        ('timestamp', 'timestamp'), ('audit.sender_core.confirmation', 'senderCoreConfirmation'),
        ('audit.output_core.confirmation', 'outputCoreConfirmation'),
        ('audit.metadata.policy.ring_id', 'ringId'), ('audit.metadata.policy.policy_id', 'policyId'),
        ('audit.metadata.policy.resource', 'resource'), ('audit.metadata.policy.permission', 'permission'),
    ]
    pairs += [(f'audit.metadata.salts[{i}]', name) for i, name in enumerate(
        ['senderCoreSalt', 'senderExtSalt', 'outputCoreSalt', 'outputExtSalt'])]
    pairs += [('audit.metadata.audit_epoch', 'auditEpoch')]
    for i, semantic in enumerate(['sender', 'recipient']):
        pairs += [(f'audit.ownership[{i}].{field}', f'{semantic}Ownership{name}')
                  for field, name in [('r.x', 'RX'), ('r.y', 'RY'), ('c.x', 'CX'), ('c.y', 'CY')]]
    result = [('self.' + source, semantic) for source, semantic in pairs]
    if len(result) != 64 or len({p for p, _ in result}) != 64 or len({s for _, s in result}) != 64:
        raise ValueError('invalid independent semantic role map')
    return result


def generate(export):
    if export.get('subject') != 'Transfer Rust structural field projection':
        raise ValueError('wrong statement projection subject')
    expected = roles()
    if export.get('paths') != [path for path, _ in expected]:
        raise ValueError('actual Rust projection differs from independent semantic role order')
    names = dict(expected)
    projected = ', '.join('s.' + names[path] for path in export['paths'])
    return f'''import ShielddSecurity.TransferStatement

set_option maxHeartbeats 200000

namespace ShielddSecurity.RuntimeTransferStatement

-- Generated from the closed AST extraction; extraction and role interpretation
-- are reviewed trust boundaries. This checks the complete ordered field list,
-- not Rust semantics, byte canonicality, or a hash/circuit correspondence.
def rustProjection {{F : Type}} (s : TransferStatement F) : List F :=
  [{projected}]

theorem projection_exact {{F : Type}} (s : TransferStatement F) :
    rustProjection s = s.fields := by
  rfl

theorem projection_injective {{F : Type}} :
    Function.Injective (rustProjection (F := F)) := by
  intro a b same
  exact TransferStatement.fields_injective
    ((projection_exact a).symm.trans (same.trans (projection_exact b)))

#print axioms projection_exact
#print axioms projection_injective

end ShielddSecurity.RuntimeTransferStatement
'''


def controls(export):
    """Identity/order controls; these are not underconstraint counterexamples."""
    from copy import deepcopy
    generate(export)
    changes = {
        'recipient/change swap': lambda p: p.__setitem__(slice(3, 7), p[5:7] + p[3:5]),
        'omit first nullifier': lambda p: p.pop(16),
        'ownership helper coordinate swap': lambda p: p.__setitem__(slice(56, 58), p[56:58][::-1]),
        'rename source field': lambda p: p.__setitem__(0, 'self.spend_auth.rk.x'),
    }
    for name, change in changes.items():
        mutant = deepcopy(export)
        change(mutant['paths'])
        try:
            generate(mutant)
        except ValueError as error:
            if 'role order' not in str(error):
                raise AssertionError(f'{name}: wrong rejection cause') from error
        else:
            raise AssertionError(f'{name}: altered projection accepted')
    return {'scope': 'semantic field/order mapping controls', 'rejected': list(changes)}


def source_controls(source, extract, work):
    """Run the actual extractor on isolated source mutants, never live runtime.

    `extract(directory)` must execute the already compiled, pinned extractor and
    return its CompletedProcess (without treating expected nonzero as success).
    This checks closed-interpreter behavior, not cryptographic soundness. Compiler
    or infrastructure errors never match the required semantic rejection marker.
    """
    import json
    from pathlib import Path
    from tempfile import TemporaryDirectory

    files = ['lib.rs', 'transfer.rs', 'encryption.rs', 'audit.rs', 'group.rs']
    source = Path(source)
    originals = {name: (source / name).read_text(encoding='utf-8') for name in files}
    # Successful real extraction is mandatory before interpreting any failure.
    original = extract(source)
    if original.returncode != 0:
        raise RuntimeError('original statement extraction did not succeed')
    generate(json.loads(original.stdout))

    cases = [
        ('loop accumulator shadow', 'transfer.rs',
         'for o in &self.outputs {',
         'for o in &self.outputs { let f = vec![self.anchor.clone()];',
         'shadowed or duplicate projection binding'),
        ('record Clone', 'audit.rs', 'self.r.x.clone(),', 'self.r.clone(),',
         'record or nested aggregate Clone unsupported'),
        ('conditional method', 'transfer.rs',
         'pub fn fields(&self) -> [F; STATEMENT_FIELDS] {',
         '#[cfg(any())]\n    pub fn fields(&self) -> [F; STATEMENT_FIELDS] {',
         'unsupported attribute'),
        ('module dispatch', 'lib.rs', 'pub mod transfer;',
         '#[path = "other.rs"]\npub mod transfer;', 'unsupported attribute'),
        ('array width', 'transfer.rs', 'pub outputs: [OutputStatement<F>; 2],',
         'pub outputs: [OutputStatement<F>; 3],', 'Transfer projection width is not 64'),
        ('unknown conditional expression', 'transfer.rs',
         'self.anchor.clone()];', 'if true { self.anchor.clone() } else { self.anchor.clone() }];',
         'unsupported projection expression'),
        ('helper coordinate order', 'audit.rs',
         'self.r.x.clone(),\n            self.r.y.clone(),',
         'self.r.y.clone(),\n            self.r.x.clone(),', None),
    ]
    results = []
    Path(work).mkdir(parents=True, exist_ok=True)
    for name, file, before, after, marker in cases:
        if originals[file].count(before) != 1:
            raise ValueError(f'{name}: mutation target changed or ambiguous')
        with TemporaryDirectory(prefix='statement-', dir=work) as temporary:
            target = Path(temporary)
            for filename, text in originals.items():
                (target / filename).write_text(text.replace(before, after) if filename == file else text,
                                              encoding='utf-8', newline='\n')
            result = extract(target)
            if marker is not None:
                if result.returncode == 0 or marker not in result.stderr:
                    raise AssertionError(f'{name}: intended AST rejection not observed: {result.stderr}')
            else:
                if result.returncode != 0:
                    raise AssertionError(f'{name}: extractor failed before the role-order check')
                try:
                    generate(json.loads(result.stdout))
                except ValueError as error:
                    if 'role order' not in str(error):
                        raise AssertionError(f'{name}: wrong rejection cause') from error
                else:
                    raise AssertionError(f'{name}: changed helper order accepted')
        results.append(name)
    return {'scope': 'actual AST interpreter rejection and helper-order controls', 'rejected': results}
