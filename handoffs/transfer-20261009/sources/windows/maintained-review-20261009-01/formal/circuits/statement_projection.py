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
        ('routing_tags[0]', 'routingSlot0'), ('routing_tags[1]', 'routingSlot1'),
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


def _native_tokens(text):
    """Closed lexical source guard, not a Rust interpreter or name resolver."""
    import re
    pattern = re.compile(r'\s+|//[^\n]*|/\*|"(?:\\[\s\S]|[^"\\])*"|\'(?:\\.|[^\'\\])\'|'
                         r'[A-Za-z_][A-Za-z_0-9]*|[0-9]+(?:[A-Za-z_][A-Za-z_0-9]*)?|'
                         r'::|=>|->|==|!=|<=|>=|&&|\|\||[{}()\[\],.;:?&*!+\-/<>|=\'#%^$@]')
    result, index = [], 0
    while index < len(text):
        match = pattern.match(text, index)
        if match is None:
            raise ValueError('unsupported native source token at offset ' + str(index))
        token = match.group()
        index = match.end()
        if token == '/*':
            depth = 1
            while depth:
                opening, closing = text.find('/*', index), text.find('*/', index)
                if closing < 0:
                    raise ValueError('unterminated native source comment')
                if 0 <= opening < closing:
                    depth += 1
                    index = opening + 2
                else:
                    depth -= 1
                    index = closing + 2
        elif not token.isspace() and not token.startswith('//'):
            result.append(token)
    return result


def _native_function(text, name):
    tokens = _native_tokens(text)
    matches = [i for i in range(len(tokens) - 2)
               if tokens[i:i+3] == ['fn', name, '(']]
    if len(matches) != 1:
        raise ValueError('missing or ambiguous native function ' + name)
    start = matches[0]
    # Attribute-selected declarations are outside this reviewed source guard.
    visibility = start
    if tokens[max(0, start-4):start] == ['pub', '(', 'crate', ')']:
        visibility -= 4
    elif start and tokens[start-1] == 'pub':
        visibility -= 1
    if visibility and tokens[visibility-1] == ']':
        raise ValueError('unsupported native function attribute ' + name)
    opening = tokens.index('{', start)
    depth = 1
    index = opening + 1
    while index < len(tokens) and depth:
        depth += (tokens[index] == '{') - (tokens[index] == '}')
        index += 1
    if depth:
        raise ValueError('unterminated native function ' + name)
    return tokens[opening+1:index-1]


def _native_impl_method(text, declaration, name):
    tokens, prefix = _native_tokens(text), _native_tokens(declaration)
    matches = [i for i in range(len(tokens)-len(prefix)+1) if tokens[i:i+len(prefix)] == prefix]
    if len(matches) != 1:
        raise ValueError('missing or ambiguous native impl ' + declaration)
    start = matches[0]
    if start and tokens[start-1] == ']':
        raise ValueError('unsupported native impl attribute')
    opening = start + len(prefix)
    if tokens[opening] != '{':
        raise ValueError('native impl declaration changed')
    depth, index = 1, opening + 1
    while index < len(tokens) and depth:
        depth += (tokens[index] == '{') - (tokens[index] == '}')
        index += 1
    if depth:
        raise ValueError('unterminated native impl')
    return _native_function(' '.join(tokens[opening+1:index-1]), name)


def native_source_arguments(sources):
    """Check reviewed owned argument construction and expose its exact sources.

    This guard establishes syntactic source bindings only. Complete Rust type,
    import/method/macro resolution, primitive codecs, source decoding and actual
    LC/native refinement remain explicit obligations. Callers retain identities
    of full source files and the exact lock; this returns no proof certificate.
    """
    paths = {
        'public': 'crates/core/component/shielded-pool/src/public_input_hash.rs',
        'handler': 'crates/core/component/shielded-pool/src/component/action_handler/transfer.rs',
        'volume': 'crates/core/component/shielded-pool/src/volume_accumulator.rs',
        'proof': 'crates/core/component/shielded-pool/src/transfer/proof.rs',
        'key': 'crates/core/keys/src/lib.rs',
        'primitive': 'crates/crypto/primitives/src/encoding.rs',
        'codec': 'crates/crypto/circuits/src/encoding.rs',
        'transaction': 'crates/core/transaction/src/transaction.rs',
        'coordinates': 'crates/crypto/primitives/src/audit.rs',
        'action': 'crates/core/component/shielded-pool/src/transfer/action.rs',
    }
    if set(sources) != set(paths.values()) or any(type(text) is not str for text in sources.values()):
        raise ValueError('native source input set differs from reviewed ten files')

    public = [
        ('rk', 'point(&encoding::nonidentity(&<[u8; 32]>::from(p.rk))?)'),
        ('anchor', 'p.anchor.into()'),
        ('outputs', '''p.outputs.iter().map(|o| transfer::OutputStatement {
            note: o.note_commitment.0, recovery: o.recovery_commitment.0,
        }).collect::<Vec<_>>().try_into()
          .map_err(|_| anyhow::anyhow!("transfer output shape"))?'''),
        ('balance', 'point(&p.balance_commitment.0)'),
        ('routing_tags', 'p.routing.tags.map(|tag| Fq::from(u64::from(tag.value)))'),
        ('routing_parameter', 'p.routing_parameter_set_id'),
        ('volume', 'volume(&p.volume_accumulator, p.proof_context.as_field())'),
        ('spends', '''p.inputs.iter().map(|i| spend(i.nullifier)).collect::<Result<Vec<_>>>()?
            .try_into().map_err(|_| anyhow::anyhow!("transfer input shape"))?'''),
        ('asset_anchor', 'p.asset_anchor.0'), ('compliance_anchor', 'p.compliance_anchor.0'),
        ('audit', 'audit(&p.compliance, p.target_timestamp)?'), ('timestamp', 'p.target_timestamp'),
    ]
    expected = 'p.validate_shape()?; Ok(transfer::Statement {' + ''.join(
        name + ': ' + expr + ',' for name, expr in public) + '})'
    if _native_function(sources[paths['public']], 'transfer_statement') != _native_tokens(expected):
        raise ValueError('native Transfer statement argument binding changed')

    guards = [
        ('public', 'point', 'let [x,y] = point_fields(point); Point {x,y}'),
        ('public', 'volume', '''transfer::VolumeStatement {
            nullifier:v.nullifier.0, commitment:v.commitment.0, day_start:Fq::from(v.day_start), context,
        }'''),
        ('public', 'transfer_statement_hash_from_public',
         'transfer_statement_hash(&transfer_statement_fields(p)?)'),
        ('public', 'transfer_statement_fields', 'Ok(transfer_statement(public)?.fields().to_vec())'),
        ('public', 'transfer_statement_hash',
         'hash(domains::TRANSFER_STATEMENT, fields, transfer::STATEMENT_FIELDS,)'),
        ('public', 'hash', '''ensure!(fields.len() == count,
            "statement expects {count} fields, got {}", fields.len()); Ok(poseidon::hash(domain,fields))'''),
        ('volume', 'as_field', 'Fq::from(match self {Self::Ordinary => 1u64,Self::FeeFunding => 2u64,})'),
        ('key', 'ensure_nonidentity_spend_auth_key', '''use anyhow::Context;
            shieldd_sdk_crypto::encoding::nonidentity(&(*key).into())
                .with_context(|| format!("invalid {role}"))?; Ok(())'''),
        ('primitive', 'point', '''let point: SubgroupPoint = Option::from(SubgroupPoint::from_bytes(bytes))
            .ok_or_else(|| anyhow::anyhow!("invalid Jubjub subgroup point"))?;
            ensure!(point.to_bytes() == *bytes,"noncanonical Jubjub point"); Ok(point)'''),
        ('primitive', 'nonidentity', '''let point = point(bytes)?;
            ensure!(!bool::from(point.is_identity()),"identity Jubjub key"); Ok(point)'''),
        ('codec', 'field', '''use commonware_codec::Read;
            use commonware_cryptography::bls12381::primitives::group::ScalarReadCfg;
            let mut bytes = value.to_bytes(); bytes.reverse();
            Scalar::read_cfg(&mut bytes.as_slice(), &ScalarReadCfg::AllowZero)
                .expect("same BLS12-381 scalar field")'''),
        ('transaction', 'decode_canonical', '''let tx: Self = pbt::Transaction::decode(bytes)
            .context("decoding transaction protobuf")?.try_into()?;
            let canonical: Vec<u8> = (&tx).into();
            anyhow::ensure!(canonical == bytes,"transaction bytes are not the canonical protobuf encoding"); Ok(tx)'''),
        ('transaction', 'context', 'TransactionContext {anchor:self.anchor,effect_hash:self.effect_hash(),}'),
        ('transaction', 'binding_sig', '&self.binding_sig'),
        ('transaction', 'transaction_body', 'self.transaction_body.clone()'),
        ('coordinates', 'point_fields', '''let Coordinates {x,y} = coordinates(point);
            [Fq::from_bytes(&x).unwrap(),Fq::from_bytes(&y).unwrap()]'''),
        ('proof', 'to_batch_item', '''let envelope = crate::proof::decode(&self.inner,
            shieldd_sdk_circuits::proof::Family::Transfer)?;
            Ok(shieldd_sdk_proof_params::pari::Verification {
                family: shieldd_sdk_circuits::proof::Family::Transfer,
                statement: shieldd_sdk_circuits::encoding::field(&public.statement_hash()?), envelope,
            })'''),
    ]
    for role, name, body in guards:
        if _native_function(sources[paths[role]], name) != _native_tokens(body):
            raise ValueError('native argument/codec wrapper changed: ' + role + '::' + name)

    decoded = '''let body: TransferBody = proto.body
        .ok_or_else(|| anyhow::anyhow!("missing transfer body"))?.try_into().context("malformed transfer body")?;
        body.validate_shape()?;
        let auth_sig = proto.auth_sig.ok_or_else(|| anyhow::anyhow!("missing action spend signature"))?.try_into()?;
        Ok(Self {body,auth_sig,proof:proto.proof.ok_or_else(|| anyhow::anyhow!("missing transfer proof"))?
            .try_into().context("malformed transfer proof")?,})'''
    if _native_impl_method(sources[paths['action']], 'impl TryFrom<pb::Transfer> for Transfer',
                           'try_from') != _native_tokens(decoded):
        raise ValueError('native full Transfer decoder source binding changed')

    handler = [
        ('rk', 'transfer.body.rk'), ('anchor', 'context.anchor'),
        ('balance_commitment', 'transfer.body.balance_commitment'),
        ('asset_anchor', 'transfer.body.asset_anchor'),
        ('compliance_anchor', 'transfer.body.compliance_anchor'),
        ('target_timestamp', 'shieldd_sdk_crypto::Fq::from(transfer.body.target_timestamp)'),
        ('inputs', 'inputs'), ('outputs', 'outputs'),
        ('compliance', 'transfer_compliance_public_from_parts(&ciphertext,&metadata)?'),
        ('routing', 'transfer.body.routing'),
        ('routing_parameter_set_id', 'transfer.body.routing_parameter_set_id'),
        ('volume_accumulator', '''VolumeAccumulatorPublic {nullifier:transfer.body.volume_accumulator.nullifier,
            commitment:transfer.body.volume_accumulator.commitment,day_start:transfer.body.volume_accumulator.day_start,}'''),
        ('proof_context', 'transfer.body.proof_context'),
    ]
    before = '''let inputs = transfer.body.inputs.iter().map(|input| {
        Ok(TransferSpendPublic {nullifier:input.nullifier,})
    }).collect::<Result<Vec<_>>>()?;
    let (ciphertext,metadata) = parse_transfer_output_compliance(&transfer.body.outputs)?;
    let outputs = transfer.body.outputs.iter().map(|output| {
        Ok(TransferOutputPublic {note_commitment:output.note_payload.note_commitment,
            recovery_commitment:output.note_payload.recovery_capsule.as_ref()
                .ok_or_else(|| anyhow::anyhow!("missing transfer recovery capsule"))?.commitment(),})
    }).collect::<Result<Vec<_>>>()?;'''
    expected = before + 'let public = TransferProofPublic {' + ''.join(
        name + (':' + expr if name != expr else '') + ',' for name, expr in handler) + '''};
        public.validate_shape().context("transfer proof shape mismatch")?; Ok(public)'''
    if _native_function(sources[paths['handler']], 'transfer_extract_public') != _native_tokens(expected):
        raise ValueError('native retained action/public source binding changed')
    return {'subject': 'Transfer owned native source argument bindings', 'schema_version': 1,
            'public_constructor': public, 'retained_action_constructor': handler,
            'contexts': {'Ordinary': 1, 'FeeFunding': 2},
            'checked_wrappers': [role + '::' + name for role, name, _ in guards],
            'complete_action_decoder': 'TryFrom<pb::Transfer> for Transfer::try_from',
            'full64_order': roles(), 'scope': 'closed lexical source argument/codec guards only',
            'translation_boundary': 'lexer + reviewed expected expressions; Rust imports/types/macros/semantics OPEN',
            'kernel_run': False, 'native_run': False, 'evidence': [], 'gates': 'OPEN'}
