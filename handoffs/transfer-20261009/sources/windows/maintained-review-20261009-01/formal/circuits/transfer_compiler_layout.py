"""Reviewed allocation tail and typed four-spool layout, not Rust refinement.

The caller supplies metadata already accepted by the existing four-spool
qualifier and all four retained shape records. This helper never accepts a
capture itself or promotes proof/evidence. Whole-file identities bind reviewed
bodies; the bodies and independent symbolic allocation proof explain the count.
"""
import hashlib
import re
from .transfer_relation import RelationError, record, natural, indices

PIN = '844389ee069e1fb2e576708842d0b389b4d9a44a'
SOURCE_CONTRACTS = {
    'crates/crypto/circuits/src/transfer.rs': {
        'sha256': 'c94460ee3c389cb0a980c9fd6289aa488bda0c71401989913160b2bdddf5d266',
        'guards': ['let var = |s: &Scalar| Var::witness(ctx, |_| s.clone());',
            'for ciphertext in &self.audit.ownership { f.extend(ciphertext.fields()); }',
            'let claimed = var(claimed_statement); params.circuit(STATEMENT_DOMAIN, &statement.fields()).assert_eq(&claimed); vec![claimed, blinding]']},
    'crates/crypto/circuits/src/audit.rs': {
        'sha256': '77f8c67817d0a247d91d012444406929deba7f307e46b5acc9febf51cbd258af',
        'guards': ['pub fn fields(&self) -> [F; 4] { [ self.r.x.clone(), self.r.y.clone(), self.c.x.clone(), self.c.y.clone(), ] }']},
    'crates/crypto/circuits/src/catalogue.rs': {
        'sha256': '98ad0d67ccb1454fd7447863c78bf5012516ad09c992f10df0b613d2ed2b6d5a',
        'guards': ['let (c, selected) = circuit::build(|ctx| w.constrain(ctx, &p, &g, &Scalar::zero()));',
            'let layout = InputLayout::new(vec![selected[0]], vec![vec![selected[1]]])?;']},
    'crates/crypto/circuits/src/hash.rs': {
        'sha256': '5cfeb1e3f0b7c0f931e8f7bd5f9f40a395f634a9f290d69a3eef108da7207a71',
        'guards': ['let output = self.hash(domain, inputs, |value| Var::native(value.clone()));',
            'let square = value.clone() * &*value;', '*value = square.clone() * &square * &*value;',
            'sum + &(lift(coefficient) * value)']},
    'third_party/commonware/cryptography/src/zk/circuit.rs': {
        'sha256': 'c5e9297c743a23a4fe855f8b8f84df519b1e42b89c5bd8fe7761d3ed83da547f',
        'guards': ['let next = CircuitIdx::Witness(self.witnesses); self.witnesses += 1; next',
            'ctx.witness(init)', 'self.merge(rhs, |a, b| a.clone() + b, CircuitNode::Add)',
            'self.merge(rhs, |a, b| a.clone() * b, CircuitNode::Mul)',
            'circuit.next_constant(combined)',
            'self.allocate(|values| Some(init(values)), |circuit| circuit.next_node(n))',
            'let new_idx = ctx.node(node(a_idx, b_idx), move |v| combine(&v[a_idx], &v[b_idx]));',
            'fn zero() -> Self { Self { inner: VarInner::Native(F::zero()), } }',
            'self.inner.circuit.lock().assertions.push((a, b));']},
    'third_party/commonware/cryptography/src/zk/pari/circuit.rs': {
        'sha256': 'cabc311936ffd8feccdf02fd097e7482faa386baaed62aedd8acb52da4ab18b7',
        'guards': ['let public_end = checked_add(1, layout.public.len())?;',
            'let committed_end = checked_add(committed_start, layout.committed_len())?;',
            'let witnesses = usize::try_from(circuit.witnesses).map_err(|_| Error::SizeOverflow)?;',
            'let next_column = checked_add(committed_end, witnesses)?;',
            'witness_columns.extend(committed_end..next_column);',
            'let column = self.next_column; self.next_column = self.next_column.checked_add(1).ok_or(Error::SizeOverflow)?;']},
}


def review_sources(sources):
    if not isinstance(sources,dict) or set(sources)!=set(SOURCE_CONTRACTS):
        raise RelationError('compiler layout exact source inventory')
    for path,contract in SOURCE_CONTRACTS.items():
        data=sources[path]
        if not isinstance(data,bytes) or len(data)>512*1024:
            raise RelationError('compiler layout bounded source bytes')
        try:normalized=re.sub(r'\s+','',data.decode('utf8'))
        except UnicodeError as error:raise RelationError('compiler layout source encoding') from error
        if any(re.sub(r'\s+','',guard) not in normalized for guard in contract['guards']):
            raise RelationError('compiler layout reviewed operation changed: '+path)
        if hashlib.sha256(data).hexdigest()!=contract['sha256']:
            raise RelationError('compiler layout reviewed source identity changed: '+path)
    return dict(pin=PIN,files={path:contract['sha256'] for path,contract in SOURCE_CONTRACTS.items()},
        status='reviewed source contracts; Rust-to-symbolic allocation correspondence remains open')


def derive_layout(accepted_metadata, shape_bytes, sources):
    """Decode already qualified shape operands and derive the symbolic origin.

    Acceptance flags are a prerequisite, never an output of this function.
    Ordinary/observer ordered row and repeated-observation equality must have
    been established by the existing exporter before calling this helper.
    """
    reviewed=review_sources(sources)
    if (not isinstance(accepted_metadata,dict) or
            accepted_metadata.get('ordinary_full_ordered_rows_equal') is not True or
            accepted_metadata.get('repeated_observations_equal') is not True):
        raise RelationError('already qualified four-spool metadata required')
    if not isinstance(shape_bytes,list) or len(shape_bytes)!=4:
        raise RelationError('all four retained spool shapes required')
    shapes=[]
    keys={'schema','compilation','relation_digest','domain_size','full_rows','public_inputs',
        'blocks','source_public','source_blocks'}
    for data in shape_bytes:
        if not isinstance(data,bytes) or len(data)>8192:raise RelationError('bounded spool layout')
        shape=record(data)
        if set(shape)!=keys or shape['schema']!='shieldd-transfer-ordered-spool-v1':
            raise RelationError('compiler layout closed shape schema')
        if shape['compilation'] not in ('observer','ordinary'):
            raise RelationError('compiler layout compilation kind')
        for field in ('domain_size','full_rows','public_inputs'):natural(shape[field])
        indices(shape['source_public'])
        if not isinstance(shape['blocks'],list) or not isinstance(shape['source_blocks'],list):
            raise RelationError('typed committed block layout required')
        for size in shape['blocks']:natural(size)
        for block in shape['source_blocks']:indices(block)
        if (shape['public_inputs']!=1 or shape['blocks']!=[1] or
                shape['source_public']!=[[1,22734]] or shape['source_blocks']!=[[[1,6]]]):
            raise RelationError('exact Transfer public/committed source layout required')
        for field in ('relation_digest','domain_size','full_rows'):
            if shape[field]!=accepted_metadata.get(field):raise RelationError('compiler layout accepted identity mismatch')
        shapes.append(shape)
    if sorted(shape['compilation'] for shape in shapes)!=['observer','observer','ordinary','ordinary']:
        raise RelationError('two ordinary and two observer shapes required')
    common=[{key:value for key,value in shape.items() if key!='compilation'} for shape in shapes]
    if any(shape!=common[0] for shape in common[1:]):raise RelationError('four-spool exact layout mismatch')
    index=common[0]['source_public'][0][1]
    witnesses=index+1
    origin=1+common[0]['public_inputs']+sum(common[0]['blocks'])+witnesses
    return dict(schema='shieldd-transfer-compiler-layout-source-v1',source_contracts=reviewed,
        layout=common[0],last_witness_index=index,witness_count=witnesses,product_origin=origin,
        interpretation='Transfer final claimed witness followed only by native constants/Add/Mul/assertion; successful nonoverflowing Context allocation; exact Compiler::new column layout',
        scope='typed qualified layout operands and reviewed source derivation; symbolic kernel proof and Rust correspondence remain separate; no evidence promotion')
