"""Bounded local-block canonical balance certificate generator (candidate only)."""
import json
from .transfer_canonical_balance import inspect, ORDER, P


def generate(metadata_bytes, stream, expected_relation):
    checked=inspect(metadata_bytes,stream,expected_relation)
    return generate_checked(json.loads(metadata_bytes), checked)


def generate_checked(m, checked, private_remainder=False, terminal_only=False):
    """Render already validated canonical comparison templates."""
    return _render(m, checked, private_remainder, terminal_only, False)


def generate_linear_checked(m, checked):
    """Render row-derived LCs, without constructing observer source handles.

    The caller must validate every LC and its exact row certificate. This
    rendering entry point does not qualify observations or accept an extraction.
    """
    return _render(m, checked, True, False, True)


def _render(m, checked, private_remainder, terminal_only, linear_values):
    copy=m['constant_copy']
    expressions={} if linear_values else {tuple(e['source']):[(c,int(v,16)) for c,v in e['terms']] for e in m['expressions']}
    raw={r['row']:r for r in checked['selected_rows']}
    roles={role:r['row'] for r in checked['templates'] for role in r['roles']}
    products={p['step']:p['rows'] for p in checked['products']}
    def lc(v):
        if linear_values: return v
        return expressions[tuple(v['source'])] if 'source' in v else [(0,int(v['native'],16))]
    def linear(terms):return '['+', '.join(f'({c}, {v})' for c,v in terms if v)+']'
    def row(r,unoutline=False):
        def terms(key):return [(0 if unoutline and c==copy else c,int(v,16)) for c,v in r[key]]
        return '⟨'+linear(terms('a'))+', '+linear(terms('b'))+'⟩'
    def step(i):
        before,left,right,factor,product,after=m['steps'][i]
        data='.foldedLeft 1' if i==0 else '.product '+linear([(0 if c==copy else c,int(v,16)) for c,v in raw[products[i][0]]['b']])
        return '⟨'+', '.join([linear(lc(before)),linear(lc(left)),linear(lc(after)),
            'true' if int(right['native'],16) else 'false',linear(lc(factor)),linear(lc(product)),data])+'⟩'
    chunks=[list(range(i,min(i+16,252))) for i in range(0,252,16)]
    names=[f'c{i}' for i in range(len(chunks))]
    bit_terms=[lc(m['steps'][i][1]) for i in range(252)]
    singleton_bits=all(len(terms)==1 and terms[0][1]==1 for terms in bit_terms)
    text=['import ShielddSecurity.TransferCanonicalBalance','import ShielddSecurity.ScalarChunkComposition',
          'set_option maxHeartbeats 500000','set_option maxRecDepth 2048',
          'namespace ShielddSecurity.RuntimeTransferCanonicalBalance',
          'open Compiler ScalarRows ScalarBits ScalarComparisonBounds ScalarChunkComposition',
          f'def p : Nat := {P}',f'def copyColumn : Nat := {copy}']
    if singleton_bits:text.insert(2,'import ShielddSecurity.ScalarBitReconstruction')
    for name,indices in zip(names,chunks):
        selected=[roles['boolean'+str(i)] for i in indices]+[r for i in indices for r in products.get(i,[])]
        text += [f'def {name}OriginalIndices : List Nat := '+str(selected),
                 f'def {name}Raw : List Row := ['+', '.join(row(raw[i]) for i in selected)+']',
                 f'def {name}Rows : List Row := unoutlineRows copyColumn {name}Raw',
                 f'def {name}Steps : List StepData := ['+', '.join(step(i) for i in indices)+']',
                 f'def {name}Initial : Linear := '+linear(lc(m['steps'][indices[0]][0])),
                 f'theorem {name}chain : checkChain p {name}Rows {name}Initial {name}Steps = true := by decide',
                 f'theorem {name}bits : checkBits p {name}Rows ({name}Steps.map StepData.left) = true := by decide',
                 f'theorem {name}endpoint (initial : Linear) : endpoint initial {name}Steps = '+linear(lc(m['steps'][indices[-1]][5]))+' := rfl']
    tail_keys=['constant-copy','reconstruction'] if terminal_only else ['constant-copy','reconstruction','endpoint'] if private_remainder else ['constant-copy','reconstruction','committed-link','endpoint']
    tail_indices=[roles[key] for key in tail_keys]
    text += ['def tailOriginalIndices : List Nat := '+str(tail_indices),
             'def tailRaw : List Row := ['+', '.join(row(raw[i]) for i in tail_indices)+']',
             'def originalBlocks : List (List Row) := ['+', '.join(name+'Raw' for name in names)+', tailRaw]',
             'def originalRows : List Row := originalBlocks.flatten',
             'def rows : List Row := unoutlineRows copyColumn originalRows',
             'def chunks : List (List StepData) := ['+', '.join(name+'Steps' for name in names)+']',
             'def steps : List StepData := chunks.flatten',
             'def privateValue : Linear := '+linear(m['value'] if linear_values else expressions[tuple(m['value'])]),
             'theorem block_included (block : List Row) (member : block ∈ originalBlocks) : ∀ r ∈ unoutlineRows copyColumn block, r ∈ rows := by\n  intro r present\n  obtain ⟨original, inside, rfl⟩ := List.mem_map.mp present\n  exact List.mem_map.mpr ⟨original, List.mem_flatten.mpr ⟨block, member, inside⟩, rfl⟩']
    for name in names:
        text += [f'theorem {name}included : ∀ r ∈ {name}Rows, r ∈ rows :=\n  block_included {name}Raw (by simp only [originalBlocks, List.mem_cons, List.mem_singleton]; simp)',
                 f'theorem {name}chain_global : checkChain p rows {name}Initial {name}Steps = true :=\n  chain_check_lift p {name}Rows rows {name}included {name}Initial {name}Steps {name}chain',
                 f'theorem {name}bits_global : checkBits p rows ({name}Steps.map StepData.left) = true :=\n  bits_check_lift p {name}Rows rows {name}included _ {name}bits']
    global_checks='true'
    for name in reversed(names): global_checks=f'(checkChain p rows {name}Initial {name}Steps && {global_checks})'
    text += ['theorem checked_chunks : checkChunks p rows [(0, 1)] chunks = true := by\n  simp only [chunks, checkChunks]\n  '+ '\n  '.join('rw ['+name+'endpoint]' for name in names[:-1])+ '\n  change '+global_checks+' = true\n  simp only ['+', '.join(name+'chain_global' for name in names)+', Bool.true_and]',
             'theorem checked_chain : checkChain p rows [(0, 1)] steps = true := chunks_certificate p rows [(0, 1)] chunks checked_chunks',
             'theorem checked_bits : checkBits p rows (steps.map StepData.left) = true := by\n  have checked : checkBitChunks p rows ['+', '.join('('+name+'Steps.map StepData.left)' for name in names)+'] = true := by\n    simp only [checkBitChunks, '+', '.join(name+'bits_global' for name in names)+', Bool.true_and]\n  simpa only [steps, chunks, List.flatten_cons, List.flatten_nil, List.map_append, List.map_nil, List.append_nil] using bit_chunks_certificate p rows _ checked',
             'theorem tail_included : ∀ r ∈ unoutlineRows copyColumn tailRaw, r ∈ rows :=\n  block_included tailRaw (by simp only [originalBlocks, List.mem_cons, List.mem_singleton]; simp)']
    last=names[-1]
    reconstruction='theorem checked_reconstruction : checkEquality p rows (bitLinear (steps.map StepData.left)) privateValue = true := by\n'
    if singleton_bits:
        columns=str([terms[0][0] for terms in bit_terms]);index=tail_indices.index(roles['reconstruction'])
        reconstruction+=f'''  have sameBits : steps.map StepData.left = ({columns} : List Nat).map (fun column => [(column,1)]) := by decide
  have checkedAt : (ScalarIndexed.checkRowAt p (unoutlineRows copyColumn tailRaw) {index}
      ⟨Compiler.subtract (weighted {columns} 1) privateValue,[]⟩ ||
      ScalarIndexed.checkRowAt p (unoutlineRows copyColumn tailRaw) {index}
        ⟨Compiler.subtract privateValue (weighted {columns} 1),[]⟩) = true := by decide
  have checkedLocal := ScalarBitReconstruction.checked_reconstruction_indexed p
    (unoutlineRows copyColumn tailRaw) {index} (steps.map StepData.left) {columns} privateValue sameBits checkedAt
'''
    else:
        reconstruction+='  have checkedLocal : checkEquality p (unoutlineRows copyColumn tailRaw) (bitLinear (steps.map StepData.left)) privateValue = true := by decide\n'
    reconstruction+='  exact equality_check_lift p _ rows tail_included _ _ checkedLocal'
    text += ['theorem checked_endpoint : checkEquality p rows (endpoint [(0, 1)] steps) [(0, 1)] = true := by\n  have checkedLocal : checkEquality p (unoutlineRows copyColumn tailRaw) '+linear(lc(m['steps'][-1][5]))+' [(0, 1)] = true := by decide\n  have lifted := equality_check_lift p _ rows tail_included _ _ checkedLocal\n  simpa only [steps, chunks, List.flatten_cons, List.flatten_nil, List.append_nil, endpoint, '+', '.join(name+'Steps' for name in names)+'] using lifted',
             'theorem checked_maximum : binary (steps.map StepData.right) = Scalar.order - 1 := by decide',
             reconstruction,
             'theorem checked_link : checkEquality p rows privateValue [(2, 1)] = true := by\n  have checkedLocal : checkEquality p (unoutlineRows copyColumn tailRaw) privateValue [(2, 1)] = true := by decide\n  exact equality_check_lift p _ rows tail_included _ _ checkedLocal',
             'theorem checked_copy : checkRow p originalRows ⟨[(0, 1), (copyColumn, -1)], []⟩ = true := by\n  have checkedLocal : checkRow p tailRaw ⟨[(0, 1), (copyColumn, -1)], []⟩ = true := by decide\n  apply row_check_lift p tailRaw originalRows _ _ checkedLocal\n  intro r present\n  exact List.mem_flatten.mpr ⟨tailRaw, (by simp only [originalBlocks, List.mem_cons, List.mem_singleton]; simp), present⟩',
             'theorem committed_canonical {F : Type} [Field F] [CharP F p] (rho : Nat → F)\n    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho originalRows) :\n    ∃ n : Nat, n < Scalar.order ∧ (n : F) = rho 2 := by\n  have unoutlined : Satisfies rho rows := unoutline_rows_sound rho copyColumn originalRows satisfied checked_copy\n  exact TransferCanonicalBalance.checked_committed_canonical rho one four rows unoutlined steps privateValue\n    checked_bits checked_chain checked_endpoint checked_maximum checked_reconstruction checked_link']
    if private_remainder or terminal_only:
        text[0]='import ShielddSecurity.TransferReduction'
        text=[entry.replace('RuntimeTransferCanonicalBalance','RuntimeTransferRemainder') for entry in text]
        text=[entry for entry in text if not entry.startswith('theorem checked_link') and not entry.startswith('theorem committed_canonical')]
        if not terminal_only:
            text.append('theorem actual_remainder_canonical {F : Type} [Field F] [CharP F p] (rho : Nat → F)\n    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho originalRows) :\n    ∃ r : Nat, r < Scalar.order ∧ (r : F) = eval rho privateValue := by\n  have unoutlined : Satisfies rho rows := unoutline_rows_sound rho copyColumn originalRows satisfied checked_copy\n  exact TransferReduction.checked_private_remainder rho one four rows unoutlined steps privateValue\n    checked_bits checked_chain checked_endpoint checked_maximum checked_reconstruction')
    if terminal_only:
        text=[entry.replace('RuntimeTransferRemainder','RuntimeTransferTerminal').replace('binary (steps.map StepData.right) = Scalar.order - 1','binary (steps.map StepData.right) = Scalar.lastRemainder') for entry in text if not entry.startswith('theorem checked_endpoint')]
        proof='theorem endpoint_final : endpoint [(0, 1)] steps = '+linear(lc(m['steps'][-1][5]))+' := by\n  simp only [steps, chunks, List.flatten_cons, List.flatten_nil, List.append_nil]\n'
        proof+='\n'.join('  rw [TransferReduction.endpoint_append, '+name+'endpoint]' for name in names[:-1])
        proof+='\n  exact '+names[-1]+'endpoint _'
        text.append(proof)
    audits=['checked_chain','checked_bits','checked_endpoint','checked_maximum','checked_reconstruction','checked_copy','actual_remainder_canonical'] if private_remainder else ['checked_chain','checked_bits','checked_endpoint','checked_maximum','checked_reconstruction','checked_link','checked_copy','committed_canonical']
    if terminal_only: audits=['checked_chain','checked_bits','checked_maximum','checked_reconstruction','checked_copy','endpoint_final']
    for name in audits:text+=['set_option pp.all true in',f'#check @{name}',f'#print axioms {name}']
    text+=['end ShielddSecurity.RuntimeTransferTerminal' if terminal_only else 'end ShielddSecurity.RuntimeTransferRemainder' if private_remainder else 'end ShielddSecurity.RuntimeTransferCanonicalBalance']
    return '\n\n'.join(text)+'\n',checked
