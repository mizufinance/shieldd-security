"""Generate bounded actual-row reduction, hash and partial semantic compositions."""
from .transfer_ivk_reduction import inspect_metadata, extract, P


def generate_quotient(data, ivk, stream, expected_relation):
    checked=extract(data,ivk,stream,expected_relation)
    state=inspect_metadata(data,ivk,expected_relation); m=state['metadata']; e=state['expressions']; copy=m['constant_copy']
    raw={r['row']:r for r in checked['selected_rows']}
    roles={k:t['row'] for t in checked['templates'] for k in t['roles']}
    products={p['role']:p['rows'] for p in checked['products']}
    def lin(lc): return '['+', '.join(f'({c}, {v})' for c,v in lc if v)+']'
    def obs(v): return e[tuple(v['source'])] if 'source' in v else [(0,int(v['native'],16))]
    def row(i): return '⟨'+lin([(c,int(v,16)) for c,v in raw[i]['a']])+', '+lin([(c,int(v,16)) for c,v in raw[i]['b']])+'⟩'
    steps=[]; indices=[roles[f'quotient.boolean.{i}'] for i in range(4)]
    for i,(before,left,right,factor,product,after) in enumerate(m['steps'][0]):
        pair=products.get(f'comparison.0.{i}')
        if pair:
            indices.extend(pair)
            aux=[(0 if c==copy else c,int(v,16)) for c,v in raw[pair[0]]['b']]
            proof='.product '+lin(aux)
        else: proof='.foldedLeft 1'
        steps.append('⟨'+', '.join([lin(obs(before)),lin(obs(left)),lin(obs(after)),'true' if int(right['native'],16) else 'false',lin(obs(factor)),lin(obs(product)),proof])+'⟩')
    indices += [roles[k] for k in ('constant-copy','quotient.reconstruction','quotient_end.assertion')]
    q=e[tuple(m['quotient'])]
    text=['import ShielddSecurity.TransferReduction','set_option maxHeartbeats 500000','namespace ShielddSecurity.RuntimeTransferQuotient',
          'open Compiler ScalarRows ScalarBits ScalarComparisonBounds',f'def p : Nat := {P}',f'def copyColumn : Nat := {copy}',
          'def originalIndices : List Nat := '+str(indices),'def originalRows : List Row := ['+', '.join(row(i) for i in indices)+']',
          'def rows : List Row := unoutlineRows copyColumn originalRows','def steps : List StepData := ['+', '.join(steps)+']',
          'def quotient : Linear := '+lin(q),
          'theorem checked_bits : checkBits p rows (steps.map StepData.left) = true := by decide',
          'theorem checked_chain : checkChain p rows [(0, 1)] steps = true := by decide',
          'theorem checked_endpoint : checkEquality p rows (endpoint [(0, 1)] steps) [(0, 1)] = true := by decide',
          'theorem checked_maximum : binary (steps.map StepData.right) = 8 := by decide',
          'theorem checked_reconstruction : checkEquality p rows (bitLinear (steps.map StepData.left)) quotient = true := by decide',
          'theorem checked_copy : checkRow p originalRows ⟨[(0, 1), (copyColumn, -1)], []⟩ = true := by decide',
          'theorem actual_quotient_bound {F : Type} [Field F] [CharP F p] (rho : Nat → F)\n    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho originalRows) :\n    ∃ q : Nat, q ≤ 8 ∧ (q : F) = eval rho quotient := by\n  have sat := unoutline_rows_sound rho copyColumn originalRows satisfied checked_copy\n  have bound := checked_comparison_bound rho one four rows sat steps checked_bits checked_chain checked_endpoint\n  rw [checked_maximum] at bound\n  have decoded := decoded_bits_value rho rows sat (steps.map StepData.left) checked_bits\n  have rebuilt := checked_equality rho rows sat _ quotient checked_reconstruction\n  exact ⟨_, bound, decoded.symm.trans rebuilt⟩']
    for name in ['checked_bits','checked_chain','checked_endpoint','checked_maximum','checked_reconstruction','checked_copy','actual_quotient_bound']:
        text += ['set_option pp.all true in',f'#check @{name}',f'#print axioms {name}']
    text+=['end ShielddSecurity.RuntimeTransferQuotient']
    return '\n\n'.join(text)+'\n',checked


def generate_remainder(data, ivk, stream, expected_relation):
    """Reuse bounded 16-step comparison blocks on actual remainder rows."""
    from .generate_transfer_canonical_balance import generate_checked
    checked=extract(data,ivk,stream,expected_relation)
    state=inspect_metadata(data,ivk,expected_relation); source=state['metadata']
    adapted=dict(source,value=source['remainder'],bits=source['remainder_bits'],
                 endpoint=source['remainder_end']['source'],steps=source['steps'][1])
    templates=[]
    for t in checked['templates']:
        roles=[]
        for role in t['roles']:
            if role.startswith('remainder.boolean.'): roles.append('boolean'+role.split('.')[-1])
            elif role=='remainder.reconstruction': roles.append('reconstruction')
            elif role=='remainder_end.assertion': roles.append('endpoint')
            elif role=='constant-copy': roles.append(role)
        if roles: templates.append({'roles':roles,'row':t['row']})
    products=[{'step':int(p['role'].split('.')[-1]),'rows':p['rows']} for p in checked['products'] if p['role'].startswith('comparison.1.')]
    sub=dict(checked,templates=templates,products=products)
    source_text,_=generate_checked(adapted,sub,private_remainder=True)
    return source_text,checked


def split_remainder(source, prefix='RuntimeTransferRemainder'):
    """Separate literal data and 16-step proofs; preserve every theorem once."""
    import re
    if not isinstance(source,str) or not isinstance(prefix,str) or not re.fullmatch('[A-Za-z][A-Za-z0-9_]*',prefix):
        raise ValueError('remainder split source/prefix')
    entries=source.strip().split('\n\n')
    namespace='ShielddSecurity.'+prefix
    data=[]; blocks={i:[] for i in range(16)}; composition=[]
    audits=[]
    for entry in entries:
        if entry.startswith('import ') or entry.startswith('set_option max') or entry.startswith('open '): data.append(entry)
        elif entry.startswith('namespace ') or entry.startswith('end '): continue
        elif entry.startswith('def ') or entry.startswith('theorem block_included'): data.append(entry)
        elif (match:=re.match(r'theorem c(\d+)(chain|bits|endpoint|included|chain_global|bits_global)\b',entry)):
            index=int(match[1])
            if index not in blocks: raise ValueError('unknown remainder chunk')
            blocks[index].append(entry)
        elif entry.startswith('set_option pp.all') or entry.startswith('#check ') or entry.startswith('#print axioms '): audits.append(entry)
        else: composition.append(entry)
    if any(len(block)!=6 for block in blocks.values()): raise ValueError('incomplete remainder chunk theorem inventory')
    for index,block in blocks.items():
        expected={f'c{index}'+suffix for suffix in ('chain','bits','endpoint','included','chain_global','bits_global')}
        names=[re.match(r'theorem (\w+)',entry)[1] for entry in block]
        if len(set(names))!=6 or set(names)!=expected: raise ValueError('remainder chunk theorem names mismatch')
    # The original namespace shares literals symbolically across all modules.
    data.insert(3,'namespace '+namespace)
    result={prefix+'Data':'\n\n'.join(data+['set_option pp.all true in','#check @block_included','#print axioms block_included','end '+namespace])+'\n'}
    for index,block in blocks.items():
        own=[]
        for theorem in block:
            name=re.match(r'theorem (\w+)',theorem)[1]
            own.extend(['set_option pp.all true in','#check @'+name,'#print axioms '+name])
        result[prefix+'Chunk'+str(index)]='\n\n'.join(['import ShielddSecurity.'+prefix+'Data','set_option maxHeartbeats 500000','namespace '+namespace,'open Compiler ScalarRows ScalarBits ScalarComparisonBounds ScalarChunkComposition',*block,*own,'end '+namespace])+'\n'
    result[prefix+'Composition']='\n\n'.join([*['import ShielddSecurity.'+prefix+'Chunk'+str(i) for i in range(16)],'set_option maxHeartbeats 500000','set_option maxRecDepth 2048','namespace '+namespace,'open Compiler ScalarRows ScalarBits ScalarComparisonBounds ScalarChunkComposition',*composition,*audits,'end '+namespace])+'\n'
    return result


def generate_terminal(data, ivk, stream, expected_relation):
    """Actual terminal comparator certificates; its endpoint is not asserted1."""
    from .generate_transfer_canonical_balance import generate_checked
    checked=extract(data,ivk,stream,expected_relation)
    state=inspect_metadata(data,ivk,expected_relation); source=state['metadata']
    adapted=dict(source,value=source['remainder'],bits=source['remainder_bits'],
                 endpoint=source['terminal_end']['source'],steps=source['steps'][2])
    templates=[]
    for t in checked['templates']:
        roles=[]
        for role in t['roles']:
            if role.startswith('remainder.boolean.'): roles.append('boolean'+role.split('.')[-1])
            elif role=='remainder.reconstruction': roles.append('reconstruction')
            elif role=='constant-copy': roles.append(role)
        if roles: templates.append({'roles':roles,'row':t['row']})
    products=[{'step':int(p['role'].split('.')[-1]),'rows':p['rows']} for p in checked['products'] if p['role'].startswith('comparison.2.')]
    sub=dict(checked,templates=templates,products=products)
    text,_=generate_checked(adapted,sub,terminal_only=True)
    return text,checked


def generate_composition(data, ivk, stream, expected_relation):
    """Symbolically compose qualified quotient and two comparator modules."""
    from .transfer_balance_rows import combine, canonical
    checked=extract(data,ivk,stream,expected_relation)
    state=inspect_metadata(data,ivk,expected_relation); m=state['metadata']; e=state['expressions']; copy=m['constant_copy']
    raw={r['row']:r for r in checked['selected_rows']}
    roles={role:t['row'] for t in checked['templates'] for role in t['roles']}
    products={p['role']:p['rows'] for p in checked['products']}
    def lin(lc): return '['+', '.join(f'({c}, {v})' for c,v in lc if v)+']'
    def pre(lc): return [(0 if c==copy else c,v) for c,v in lc]
    def decode(lc): return [(c,int(v,16)) for c,v in lc]
    def row(i): return '⟨'+lin(decode(raw[i]['a']))+', '+lin(decode(raw[i]['b']))+'⟩'
    gate=products['terminal-gate.product']; inverse=products['consumer.inverse']
    tail_indices=[roles['hash-equation'],roles['terminal-gate'],*gate,*inverse]
    aux=pre(decode(raw[inverse[0]]['b']))
    output=canonical([(c,v*pow(4,-1,P)) for c,v in combine(pre(decode(raw[inverse[1]]['b'])),aux,-1)])
    qname='RuntimeTransferQuotient'; rname='RuntimeTransferRemainder'; tname='RuntimeTransferTerminal'
    text=[f'import ShielddSecurity.{qname}',f'import ShielddSecurity.{rname}Composition',f'import ShielddSecurity.{tname}Composition',
          'set_option maxHeartbeats 500000','set_option maxRecDepth 2048','namespace ShielddSecurity.RuntimeTransferReduction',
          'open Compiler ScalarRows ScalarBits ScalarComparisonBounds ScalarChunkComposition',f'def p : Nat := {P}',f'def copyColumn : Nat := {copy}']
    for name,module in [('q',qname),('r',rname),('t',tname)]:
        text.append(f'def {name}Rows : List Row := {module}.rows')
    text += ['def tailOriginalIndices : List Nat := '+str(tail_indices),'def tailRaw : List Row := ['+', '.join(row(i) for i in tail_indices)+']',
             'def tailRows : List Row := unoutlineRows copyColumn tailRaw',
             f'def originalRows : List Row := {qname}.originalRows ++ ({rname}.originalRows ++ ({tname}.originalRows ++ tailRaw))',
             'def rows : List Row := qRows ++ (rRows ++ (tRows ++ tailRows))']
    for i,name in enumerate(['q','r','t','tail']):
        wrap='member'
        if i<3: wrap='Or.inl '+wrap
        for _ in range(i): wrap='Or.inr ('+wrap+')'
        text.append(f'theorem {name}Included : ∀ row ∈ {name}Rows, row ∈ rows := by\n  intro row member\n  simp only [rows, List.mem_append]\n  exact {wrap}')
    for prefix,module in [('q',qname),('r',rname),('t',tname)]:
        text += [f'theorem {prefix}Bits : checkBits p rows ({module}.steps.map StepData.left) = true :=\n  bits_check_lift p {prefix}Rows rows {prefix}Included _ {module}.checked_bits',
                 f'theorem {prefix}Chain : checkChain p rows [(0, 1)] {module}.steps = true :=\n  chain_check_lift p {prefix}Rows rows {prefix}Included _ _ {module}.checked_chain']
    for prefix,module in [('q',qname),('r',rname)]:
        role='quotient' if prefix=='q' else 'privateValue'
        text += [f'theorem {prefix}End : checkEquality p rows (endpoint [(0, 1)] {module}.steps) [(0, 1)] = true :=\n  equality_check_lift p {prefix}Rows rows {prefix}Included _ _ {module}.checked_endpoint',
                 f'theorem {prefix}Rebuild : checkEquality p rows (bitLinear ({module}.steps.map StepData.left)) {module}.{role} = true :=\n  equality_check_lift p {prefix}Rows rows {prefix}Included _ _ {module}.checked_reconstruction']
    for name,key in [('hash','value'),('gate','terminal_gate')]: text.append('def '+name+' : Linear := '+lin(e[tuple(m[key])]))
    text += ['def high : Linear := '+lin(e[tuple(m['quotient_bits'][3])]),
             'def lastEndpoint : Linear := '+lin(e[tuple(m['terminal_end']['source'])]),
             'def consumer : Linear := '+lin(e[tuple(m['consumer'][0])]),'def inverse : Linear := '+lin(e[tuple(m['consumer'][1])]),
             'def inverseOutput : Linear := '+lin(output),
             'def gateData : ProductData := .product '+lin(pre(decode(raw[gate[0]]['b']))),
             'def inverseData : ProductData := .product '+lin(aux)]
    checks=[('gateProduct','checkProduct p tailRows high ([(0, 1)] ++ scaleLinear (-1) lastEndpoint) gate gateData'),
            ('gateAssertion','checkEquality p tailRows gate []'),('inverseProduct','checkProduct p tailRows inverse consumer inverseOutput inverseData'),
            ('inverseAssertion','checkEquality p tailRows inverseOutput [(0, 1)]'),
            ('equation','checkEquality p tailRows (scaleLinear (Scalar.order : Int) RuntimeTransferQuotient.quotient ++ RuntimeTransferRemainder.privateValue) hash')]
    for name,expression in checks: text.append(f'theorem {name}Local : {expression} = true := by decide')
    text += [f'theorem sameRBits : {tname}.steps.map StepData.left = {rname}.steps.map StepData.left := by decide',
             'def qBits : List Linear := '+ '['+', '.join(lin(e[tuple(bit)]) for bit in m['quotient_bits'])+']',
             f'theorem qBitRoles : {qname}.steps.map StepData.left = qBits := by decide',
             f'theorem consumerRoles : canonical p consumer = canonical p (bitLinear ({rname}.steps.map StepData.left)) := by decide',
             'theorem checkedCopy : checkRow p originalRows ⟨[(0, 1), (copyColumn, -1)], []⟩ = true := by\n  apply row_check_lift p RuntimeTransferQuotient.originalRows originalRows _ _ RuntimeTransferQuotient.checked_copy\n  intro row member\n  simp only [originalRows, List.mem_append]\n  exact Or.inl member']
    main='''theorem actual_nonzero_reduction {F : Type} [Field F] [CharP F p] (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho originalRows) :
    ∃ q r : Nat, q ≤ 8 ∧ 0 < r ∧ r < Scalar.order ∧
      q * Scalar.order + r < Scalar.modulus ∧
      (q : F) = eval rho RuntimeTransferQuotient.quotient ∧
      (r : F) = eval rho RuntimeTransferRemainder.privateValue ∧
      ((q * Scalar.order + r : Nat) : F) = eval rho hash ∧
      (r : F) = eval rho consumer := by
  have mapped := unoutline_rows_sound rho copyColumn originalRows satisfied checkedCopy
  have sat : Satisfies rho rows := by
    simpa only [rows, qRows, rRows, tRows, tailRows, originalRows, unoutlineRows,
      RuntimeTransferQuotient.rows, RuntimeTransferRemainder.rows, RuntimeTransferTerminal.rows,
      RuntimeTransferQuotient.copyColumn, RuntimeTransferRemainder.copyColumn,
      RuntimeTransferTerminal.copyColumn, copyColumn, List.map_append] using mapped
  let q := binary (decodeBits rho (RuntimeTransferQuotient.steps.map StepData.left))
  let r := binary (decodeBits rho (RuntimeTransferRemainder.steps.map StepData.left))
  have qBound : q ≤ 8 := by
    have bound := checked_comparison_bound rho one four rows sat RuntimeTransferQuotient.steps qBits qChain qEnd
    simpa only [RuntimeTransferQuotient.checked_maximum] using bound
  have rBound : r < Scalar.order := checked_remainder_bound rho one four rows sat
    RuntimeTransferRemainder.steps rBits rChain rEnd RuntimeTransferRemainder.checked_maximum
  have cap : q = 8 → r ≤ Scalar.lastRemainder := by
    intro eight
    have qCheck : checkBits p rows qBits = true := by simpa only [qBitRoles] using qBits
    have product := product_check_lift p tailRows rows tailIncluded _ _ _ _ gateProductLocal
    have guard : checkProduct p rows high
        ([(0, 1)] ++ scaleLinear (-1) (endpoint [(0, 1)] RuntimeTransferTerminal.steps)) gate gateData = true := by
      simpa only [RuntimeTransferTerminal.endpoint_final, lastEndpoint] using product
    have assertion := equality_check_lift p tailRows rows tailIncluded _ _ gateAssertionLocal
    have bounded := checked_quotient_eight_cap rho one four rows sat
      (qBits[0]!) (qBits[1]!) (qBits[2]!) high RuntimeTransferTerminal.steps
      (by simpa only [qBits, high] using qCheck) tBits tChain RuntimeTransferTerminal.checked_maximum
      gate gateData guard assertion (by simpa only [q, qBitRoles, qBits, high] using eight)
    simpa only [sameRBits] using bounded
  have fieldEquation := TransferReduction.checked_role_equation rho rows sat
    (RuntimeTransferQuotient.steps.map StepData.left) (RuntimeTransferRemainder.steps.map StepData.left)
    RuntimeTransferQuotient.quotient RuntimeTransferRemainder.privateValue hash qBits rBits qRebuild rRebuild
    (equality_check_lift p tailRows rows tailIncluded _ _ equationLocal)
  have qCast := (decoded_bits_value rho rows sat _ qBits).symm.trans
    (checked_equality rho rows sat _ _ qRebuild)
  have rCast := (decoded_bits_value rho rows sat _ rBits).symm.trans
    (checked_equality rho rows sat _ _ rRebuild)
  have consumerCast : (r : F) = eval rho consumer :=
    (decoded_bits_value rho rows sat _ rBits).symm.trans
      (canonical_equal rho _ _ consumerRoles).symm
  have nonzero := TransferReduction.checked_inverse_nonzero rho one four rows sat inverse consumer inverseOutput inverseData
    (product_check_lift p tailRows rows tailIncluded _ _ _ _ inverseProductLocal)
    (equality_check_lift p tailRows rows tailIncluded _ _ inverseAssertionLocal)
  have positive : 0 < r := by
    by_contra failure
    have zero : r = 0 := by omega
    apply nonzero
    simpa only [zero, Nat.cast_zero] using consumerCast.symm
  refine ⟨q, r, qBound, positive, rBound, Scalar.reduction_sum_bound qBound rBound cap, qCast, rCast, ?_, consumerCast⟩
  simpa only [Nat.cast_add, Nat.cast_mul] using fieldEquation'''
    # Avoid shadowing qBits definition with its certificate theorem.
    text=[entry.replace('theorem qBits :','theorem qBoolean :') for entry in text]
    main=main.replace('steps qBits qChain','steps qBoolean qChain').replace('using qBits\n','using qBoolean\n').replace('hash qBits rBits','hash qBoolean rBits').replace('_ qBits).symm','_ qBoolean).symm')
    text.append(main)
    audits=['sameRBits','qBitRoles','consumerRoles','checkedCopy','actual_nonzero_reduction']+[name+'Local' for name,_ in checks]
    for name in audits: text+=['set_option pp.all true in','#check @'+name,'#print axioms '+name]
    text.append('end ShielddSecurity.RuntimeTransferReduction')
    return '\n\n'.join(text)+'\n'


def generate_hash_join():
    """Shared-rho composition of the exact existing hash and reduction modules."""
    return '''import ShielddSecurity.RuntimeIvkHash_Composition
import ShielddSecurity.RuntimeTransferReduction

set_option maxHeartbeats 500000

namespace ShielddSecurity.RuntimeTransferIvk
open Compiler

def p : Nat := RuntimeTransferReduction.p

def originalRows : List Row :=
  RuntimeHashBlock_authorization_ivk_0.rawRows ++ RuntimeTransferReduction.originalRows

theorem output_roles : canonical p RuntimeTransferReduction.hash =
    canonical p RuntimeHashBlock_authorization_ivk_0.output := by decide

theorem actual_hash_reduction {F : Type} [Field F] [CharP F p]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho originalRows) :
    ∃ q r : Nat, q ≤ 8 ∧ 0 < r ∧ r < Scalar.order ∧
      q * Scalar.order + r < Scalar.modulus ∧
      (q : F) = eval rho RuntimeTransferQuotient.quotient ∧
      (r : F) = eval rho RuntimeTransferRemainder.privateValue ∧
      ((q * Scalar.order + r : Nat) : F) =
        Poseidon.hash6 (Poseidon.castParameters RuntimeHashBlock_authorization_ivk_0.parameters) 16
          (RuntimeHashBlock_authorization_ivk_0.callInputs.map (eval rho)) ∧
      (r : F) = eval rho RuntimeTransferReduction.consumer := by
  have hashSat : Satisfies rho RuntimeHashBlock_authorization_ivk_0.rawRows := by
    intro row member
    apply satisfied row
    exact List.mem_append.mpr (Or.inl member)
  have reductionSat : Satisfies rho RuntimeTransferReduction.originalRows := by
    intro row member
    apply satisfied row
    exact List.mem_append.mpr (Or.inr member)
  have hashMeaning := RuntimeHashBlock_authorization_ivk_0.actual_hash_sound rho one hashSat
  obtain ⟨q, r, qBound, positive, rBound, noWrap, qCast, rCast, fieldHash, consumer⟩ :=
    RuntimeTransferReduction.actual_nonzero_reduction rho one four reductionSat
  have shared := canonical_equal rho RuntimeTransferReduction.hash
    RuntimeHashBlock_authorization_ivk_0.output output_roles
  exact ⟨q, r, qBound, positive, rBound, noWrap, qCast, rCast,
    fieldHash.trans (shared.trans hashMeaning), consumer⟩

set_option pp.all true in
#check @output_roles
#print axioms output_roles
set_option pp.all true in
#check @actual_hash_reduction
#print axioms actual_hash_reduction

end ShielddSecurity.RuntimeTransferIvk
'''


def generate_sem_join():
    """Canonical-codec and named-role boundary to the independent scalar clause."""
    return '''import ShielddSecurity.RuntimeTransferIvk
import ShielddSecurity.TransferSem

set_option maxHeartbeats 500000

namespace ShielddSecurity.RuntimeTransferAuthorization

theorem input_columns : RuntimeHashBlock_authorization_ivk_0.callInputs =
    [[(1993, 1)], [(1980, 1)], [(1981, 1)]] := by decide

/-- The codec is an imported primitive functional contract. The three role and
operation equalities are explicit local source/model joins, not upstream
cryptographic assumptions and not conclusions of this theorem. All numerical
reduction bounds/nonzero/equations are derived from actual row satisfaction. -/
theorem authorization_scalar_sem {F : Type} [Field F] [CharP F RuntimeTransferIvk.p]
    (codec : TransferReduction.CanonicalField F) (c : TransferSem.Crypto)
    (w : TransferSem.Witness) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho RuntimeTransferIvk.originalRows)
    (quotientRole : w.auth.quotient = codec.decode (eval rho RuntimeTransferQuotient.quotient))
    (ivkRole : w.auth.ivk = codec.decode (eval rho RuntimeTransferReduction.consumer))
    (hashOperation : c.hash .incomingViewingKey ([w.auth.nk] ++ TransferSem.pointFields w.auth.ak) =
      codec.decode (Poseidon.hash6 (Poseidon.castParameters RuntimeHashBlock_authorization_ivk_0.parameters) 16
        (RuntimeHashBlock_authorization_ivk_0.callInputs.map (eval rho)))) :
    TransferSem.AuthorizationScalarSem c w := by
  obtain ⟨q, r, qBound, positive, rBound, noWrap, qCast, rCast, hashCast, consumerCast⟩ :=
    RuntimeTransferIvk.actual_hash_reduction rho one four satisfied
  have decoded := TransferReduction.decoded_reduction codec _ _ _ q r qBound positive rBound noWrap
    qCast consumerCast hashCast
  rcases decoded with ⟨quotientBound, remainderPositive, remainderBound, equation⟩
  unfold TransferSem.AuthorizationScalarSem
  rw [quotientRole, ivkRole, hashOperation]
  exact ⟨remainderBound, Nat.ne_of_gt remainderPositive, quotientBound, equation⟩

set_option pp.all true in
#check @input_columns
#print axioms input_columns
set_option pp.all true in
#check @authorization_scalar_sem
#print axioms authorization_scalar_sem

end ShielddSecurity.RuntimeTransferAuthorization
'''


def generate_sem_operation_join():
    """Derive the one-call interpretation from bounded primitive operation use."""
    source=generate_sem_join()
    theorem='''/-- Local hash operation and named input-column interpretations are
explicit prerequisites. The actual numeric clause is still a row consequence. -/
theorem authorization_scalar_from_operations {F : Type} [Field F] [CharP F RuntimeTransferIvk.p]
    (codec : TransferReduction.CanonicalField F) (c : TransferSem.Crypto)
    (w : TransferSem.Witness) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho RuntimeTransferIvk.originalRows)
    (quotientRole : w.auth.quotient = codec.decode (eval rho RuntimeTransferQuotient.quotient))
    (ivkRole : w.auth.ivk = codec.decode (eval rho RuntimeTransferReduction.consumer))
    (nkRole : w.auth.nk = codec.decode (rho 1993))
    (akXRole : w.auth.ak.x = codec.decode (rho 1980))
    (akYRole : w.auth.ak.y = codec.decode (rho 1981))
    (hashInterpreter : ∀ nk ax ay : Nat,
      nk < Scalar.modulus → ax < Scalar.modulus → ay < Scalar.modulus →
      c.hash .incomingViewingKey [nk, ax, ay] =
        codec.decode (Poseidon.hash6 (Poseidon.castParameters RuntimeHashBlock_authorization_ivk_0.parameters) 16
          [(nk : F), (ax : F), (ay : F)])) :
    TransferSem.AuthorizationScalarSem c w := by
  have inputs : RuntimeHashBlock_authorization_ivk_0.callInputs.map (eval rho) =
      [(w.auth.nk : F), (w.auth.ak.x : F), (w.auth.ak.y : F)] := by
    rw [input_columns]
    simp only [List.map_cons, List.map_nil, eval,
      Int.cast_one, one_mul, add_zero, zero_add, nkRole, akXRole, akYRole, codec.roundtrip]
  apply authorization_scalar_sem codec c w rho one four satisfied quotientRole ivkRole
  rw [inputs]
  simpa only [TransferSem.pointFields, List.cons_append, List.nil_append] using
    hashInterpreter w.auth.nk w.auth.ak.x w.auth.ak.y
      (by rw [nkRole]; exact codec.bounded _)
      (by rw [akXRole]; exact codec.bounded _)
      (by rw [akYRole]; exact codec.bounded _)

set_option pp.all true in
#check @authorization_scalar_from_operations
#print axioms authorization_scalar_from_operations

'''
    return source.replace('end ShielddSecurity.RuntimeTransferAuthorization',theorem+'end ShielddSecurity.RuntimeTransferAuthorization')


def generate_sem_projection_join():
    """Construct just the numeric authorization projection from the shared rho."""
    source=generate_sem_operation_join()
    extension='''/-- Partial semantic witness projection. All remaining fields come from
the supplied base; this does not assert their satisfaction or native origin. -/
def scalar_projection {F : Type} [Field F] (codec : TransferReduction.CanonicalField F)
    (rho : Nat → F) (base : TransferSem.Witness) : TransferSem.Witness :=
  { base with auth := { base.auth with
      nk := codec.decode (rho 1993)
      ak := { x := codec.decode (rho 1980), y := codec.decode (rho 1981) }
      quotient := codec.decode (eval rho RuntimeTransferQuotient.quotient)
      ivk := codec.decode (eval rho RuntimeTransferReduction.consumer) } }

theorem projected_authorization_scalar {F : Type} [Field F] [CharP F RuntimeTransferIvk.p]
    (codec : TransferReduction.CanonicalField F) (c : TransferSem.Crypto)
    (base : TransferSem.Witness) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho RuntimeTransferIvk.originalRows)
    (hashInterpreter : ∀ nk ax ay : Nat,
      nk < Scalar.modulus → ax < Scalar.modulus → ay < Scalar.modulus →
      c.hash .incomingViewingKey [nk, ax, ay] =
        codec.decode (Poseidon.hash6 (Poseidon.castParameters RuntimeHashBlock_authorization_ivk_0.parameters) 16
          [(nk : F), (ax : F), (ay : F)])) :
    TransferSem.AuthorizationScalarSem c (scalar_projection codec rho base) := by
  exact authorization_scalar_from_operations codec c (scalar_projection codec rho base) rho
    one four satisfied rfl rfl rfl rfl rfl hashInterpreter

theorem projected_raw_fields_canonical {F : Type} [Field F]
    (codec : TransferReduction.CanonicalField F) (rho : Nat → F) (base : TransferSem.Witness) :
    let w := scalar_projection codec rho base
    TransferCore.CanonicalAffine w.auth.ak ∧ w.auth.nk < Scalar.modulus ∧
      w.auth.ivk < Scalar.modulus ∧ w.auth.quotient < Scalar.modulus := by
  exact ⟨⟨codec.bounded _, codec.bounded _⟩, codec.bounded _, codec.bounded _, codec.bounded _⟩

set_option pp.all true in
#check @projected_authorization_scalar
#print axioms projected_authorization_scalar
set_option pp.all true in
#check @projected_raw_fields_canonical
#print axioms projected_raw_fields_canonical

'''
    return source.replace('end ShielddSecurity.RuntimeTransferAuthorization',extension+'end ShielddSecurity.RuntimeTransferAuthorization')
