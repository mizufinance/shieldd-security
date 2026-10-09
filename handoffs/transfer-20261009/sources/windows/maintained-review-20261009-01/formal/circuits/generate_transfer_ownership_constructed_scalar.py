"""Scalar endpoint from actual constructed ownership rows, without targets.

All eight row/source joins are checked by the maintained constructor and legacy
trace validators. The semantic endpoint consumes their proved constructor
output; source routing to a native sender is a separate owned join.
"""
from . import generate_transfer_ownership_constructor_candidates as candidates
from . import generate_transfer_ownership_constructor_arithmetic as arithmetic
from . import generate_transfer_ownership_constructor_trace as trace
from . import transfer_ownership as owner
from . import generate_transfer_ivk_reduction_join as joins
import re


def generate(chunks,selections,readonly_lcs=()):
    name = 'RuntimeOwnershipConstructedScalar'
    return name, generate_modules(chunks, selections, readonly_lcs)[name]


def generate_modules(chunks,selections,readonly_lcs=()):
    candidates.validate_all_chunks(chunks,selections)
    trace.generate(chunks,selections,readonly_lcs)
    owner.generate_trace_composition(chunks,selections)
    for checked,selected in zip(chunks,selections):arithmetic.generate(checked,selected,readonly_lcs)
    bit_start=chunks[0]['derived'][chunks[0]['bits'][0]][0][0]
    return _render_modules(bit_start)


def _render(bit_start):
    """Main endpoint; compile the factored modules from ``_render_modules`` first."""
    name = 'RuntimeOwnershipConstructedScalar'
    return name, _render_modules(bit_start)[name]


def _render_combined(bit_start):
    """Pure proof template after strict typed planning; not capture ingress."""
    if type(bit_start) is not int or not 0 < bit_start <= 262144 - 252:
        raise owner.relation.RelationError('ownership scalar proof bit-column template')
    starts=list(range(0,126,16));names=[f'RuntimeOwnershipTrace{start:03d}' for start in starts]
    aliases=dict(G='RuntimeOwnershipConstructorTrace',L='RuntimeTransferOwnership',W='RuntimeOwnershipWindow000')
    name='RuntimeOwnershipConstructedScalar'
    source=''.join(f'import ShielddSecurity.RuntimeOwnershipConstructorArithmetic{start:03d}\n' for start in starts)
    source+='''import ShielddSecurity.RuntimeOwnershipConstructorTrace
import ShielddSecurity.RuntimeTransferOwnership
import ShielddSecurity.ScalarConstructedBits
import ShielddSecurity.ScalarWrittenBitValues
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
'''+f'namespace ShielddSecurity.{name}\n'
    source+=''.join(f'namespace {key} := {target}\n' for key,target in aliases.items())
    source+=f'''private theorem actual_columns : L.columns = List.range' {bit_start} 252 := by rfl
'''
    for offset,start in enumerate(starts):
        chunk=f'RuntimeOwnershipConstructorChunk{start:03d}'
        member=trace._member(offset,8,'member')
        source+=f'''private theorem chunk_equations{offset} {{F : Type}} [Field F] [CharP F L.modulus]
    (rho : Nat → F) (sourceBits : Nat → Bool) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (constructed : Satisfies rho G.originalRows)
    (written : ∀ index < 252, rho ({bit_start}+index) = if sourceBits index then 1 else 0) :
    TransferOwnership.TraceEquations (L.coefficientD : F) (L.base rho) (L.twice rho) (L.triple rho)
      ({names[offset]}.input rho) ({names[offset]}.windows rho) := by
  have chunkRows : Satisfies rho {chunk}.originalRows := by
    intro row member
    apply constructed row
    change row ∈ G.originalRows
    unfold G.originalRows
    exact {member}
  exact RuntimeOwnershipConstructorArithmetic{start:03d}.actual_trace
    rho sourceBits one four chunkRows written
'''
    for offset in range(7):
        source+=f'''private theorem boundary{offset} {{F : Type}} [Field F] (rho : Nat → F) :
    TransferOwnership.traceOutput ({names[offset]}.input rho) ({names[offset]}.windows rho) =
      {names[offset+1]}.input rho := by
  exact {names[offset]}.output_role rho
'''
    for offset in reversed(range(7)):
        suffix=names[-1]+'.windows rho'
        for following in reversed(names[offset:-1]):suffix=following+'.windows rho ++ ('+suffix+')'
        next_suffix=names[-1]+'.windows rho'
        for following in reversed(names[offset+1:-1]):next_suffix=following+'.windows rho ++ ('+next_suffix+')'
        next_helper='chunk_equations7' if offset==6 else f'tail_equations{offset+1}'
        source+=f'''private theorem tail_equations{offset} {{F : Type}} [Field F] [CharP F L.modulus]
    (rho : Nat → F) (sourceBits : Nat → Bool) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (constructed : Satisfies rho G.originalRows)
    (written : ∀ index < 252, rho ({bit_start}+index) = if sourceBits index then 1 else 0) :
    TransferOwnership.TraceEquations (L.coefficientD : F)
      (L.base rho) (L.twice rho) (L.triple rho) ({names[offset]}.input rho) ({suffix}) := by
  exact (TransferOwnership.trace_equations_append (L.coefficientD : F)
    (L.base rho) (L.twice rho) (L.triple rho) ({names[offset]}.input rho)
    ({names[offset]}.windows rho) ({next_suffix})).mpr
    ⟨chunk_equations{offset} rho sourceBits one four constructed written,
     Eq.mpr (congrArg (fun input => TransferOwnership.TraceEquations (L.coefficientD : F)
       (L.base rho) (L.twice rho) (L.triple rho) input ({next_suffix})) (boundary{offset} rho))
       ({next_helper} rho sourceBits one four constructed written)⟩
'''
    source+=f'''theorem actual_trace {{F : Type}} [Field F] [CharP F L.modulus]
    (rho : Nat → F) (sourceBits : Nat → Bool) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (constructed : Satisfies rho G.originalRows)
    (written : ∀ index < 252, rho ({bit_start}+index) = if sourceBits index then 1 else 0) :
    TransferOwnership.TraceEquations (L.coefficientD : F) (L.base rho) (L.twice rho) (L.triple rho)
      (L.input rho) (L.windows rho) := by
  exact tail_equations0 rho sourceBits one four constructed written
'''
    source+=f'''theorem scalar_coordinates {{F J : Type}} [Field F] [CharP F L.modulus] [AddCommGroup J]
    (rho : Nat → F) (n : Nat) (bounded : n < 2^252)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (imaginary : F) (model : Group.StandardCurveModel J (L.coefficientD : F))
    (nonSquare : Group.NoUnitSquare (L.coefficientD : F)) (imaginarySquare : imaginary*imaginary = -1)
    (senderBase : J) (baseRole : L.base rho = model.coordinates senderBase)
    (constructed : Satisfies rho G.originalRows)
    (written : ∀ index < 252, rho ({bit_start}+index) =
      if (encodeBits 252 n)[index]?.getD false then 1 else 0) :
    RuntimeOwnershipWindow125.result rho = model.coordinates (n • senderBase) := by
  have firstRows : Satisfies rho W.rawRows := by
    intro row member
    apply constructed row
    unfold G.originalRows
    apply List.mem_append_left
    change row ∈ RuntimeOwnershipConstructorChunk000.originalBlocks.flatten
    refine List.mem_flatten.mpr ⟨W.rawRows,?_,member⟩
    exact List.mem_cons.mpr (Or.inl rfl)
  obtain ⟨doubleRows,addRows,_,_,_,_⟩ := W.arithmetic_window rho one four firstRows
  change TransferOwnership.DoubleEquations (L.base rho) (L.twice rho) at doubleRows
  change TransferOwnership.AddEquations (L.coefficientD : F) (L.twice rho) (L.base rho) (L.triple rho) at addRows
  rw [baseRole] at doubleRows addRows
  have decoded : ScalarBits.decodeBits rho L.bits = encodeBits 252 n := by
    rw [L.bits,actual_columns]
    have preserved : ∀ column ∈ List.range' {bit_start} (encodeBits 252 n).length,
        rho column = writeBits rho {bit_start} (encodeBits 252 n) column := by
      intro column member
      obtain ⟨index,bound,position⟩ := List.mem_range'.mp member
      rw [Nat.one_mul] at position
      subst column
      exact (written index (by simpa only [encodeBits_length] using bound)).trans
        (ScalarWrittenBitValues.field_bit_value rho {bit_start} (encodeBits 252 n) index bound).symm
    have values := (List.map_congr_left preserved).trans (writeBits_map rho {bit_start} (encodeBits 252 n))
    simpa only [encodeBits_length] using ScalarConstructedBits.decoded_singletons rho _ (encodeBits 252 n) values
  have inputRole : L.input rho = model.coordinates 0 := by
    rw [model.identity]
    simp [L.input,RuntimeOwnershipTrace000.input,W.input,eval,one,Group.identityPoint]
  have equations := actual_trace rho (fun index => (encodeBits 252 n)[index]?.getD false) one four constructed written
  rw [baseRole,inputRole] at equations
  have result := TransferOwnership.trace_scalar_coordinates (L.coefficientD : F) imaginary model nonSquare imaginarySquare
    senderBase (L.twice rho) (L.triple rho) doubleRows addRows (L.windows rho)
    (ScalarBits.decodeBits rho L.bits) (L.digits_order rho) equations
  rw [← inputRole,L.output_role rho,decoded,encodeBits_value 252 n bounded] at result
  exact result
#print axioms actual_trace
#print axioms scalar_coordinates
'''
    return name,joins._qualify(source+f'end ShielddSecurity.{name}\n',aliases)


def _render_modules(bit_start):
    """Bounded proof modules after typed planning, without repeating its graph.

    Each suffix append is elaborated in an independent module. The two endpoint
    statements are retained, and all new facts require their own kernel audits.
    """
    name, combined = _render_combined(bit_start)
    namespace = 'ShielddSecurity.' + name
    header, commands = combined.split('namespace ' + namespace + '\n', 1)
    options = 'set_option maxHeartbeats 300000\nset_option maxRecDepth 4096\n'
    markers = list(re.finditer(r'^(?:private )?theorem (\w+)\b', commands, re.M))
    pieces = {marker[1]: commands[marker.start():markers[index + 1].start()
              if index + 1 < len(markers) else commands.index('set_option pp.all true in\n#check @actual_trace')]
              for index, marker in enumerate(markers)}
    expected = (['actual_columns'] + [f'chunk_equations{i}' for i in range(8)] +
                [f'boundary{i}' for i in range(7)] + [f'tail_equations{i}' for i in reversed(range(7))] +
                ['actual_trace', 'scalar_coordinates'])
    if list(pieces) != expected:
        raise owner.relation.RelationError('ownership scalar factored command inventory')

    def audit(names):
        return ''.join(f'set_option pp.all true in\n#check @{item}\n#print axioms {item}\n' for item in names)

    result = {}
    facts = 'RuntimeOwnershipConstructedTraceFacts'
    fact_names = expected[:16]
    fact_body = ''.join(pieces[item].replace('private theorem ', 'theorem ', 1) for item in fact_names)
    result[facts] = header + f'namespace ShielddSecurity.{facts}\n' + fact_body + audit(fact_names) + f'end ShielddSecurity.{facts}\n'

    for offset in reversed(range(7)):
        module = f'RuntimeOwnershipConstructedTraceTail{offset:03d}'
        next_module = f'RuntimeOwnershipConstructedTraceTail{offset + 1:03d}'
        imports = f'import ShielddSecurity.{facts}\n'
        if offset < 6:
            imports += f'import ShielddSecurity.{next_module}\n'
        body = pieces[f'tail_equations{offset}'].replace(f'private theorem tail_equations{offset}', 'theorem actual_trace', 1)
        body = re.sub(r'\bchunk_equations(\d)\b', lambda found: facts + '.chunk_equations' + found[1], body)
        body = re.sub(r'\bboundary(\d)\b', lambda found: facts + '.boundary' + found[1], body)
        if offset < 6:
            body = re.sub(r'\btail_equations' + str(offset + 1) + r'\b', next_module + '.actual_trace', body)
        result[module] = imports + options + f'namespace ShielddSecurity.{module}\n' + body + audit(['actual_trace']) + f'end ShielddSecurity.{module}\n'

    column = pieces['actual_columns'].split(' := by', 1)[0] + f' := by\n  exact {facts}.actual_columns\n'
    endpoint = pieces['actual_trace'].replace('tail_equations0', 'RuntimeOwnershipConstructedTraceTail000.actual_trace')
    scalar = pieces['scalar_coordinates']
    main_header = header.replace('set_option maxHeartbeats', 'import ShielddSecurity.RuntimeOwnershipConstructedTraceTail000\nset_option maxHeartbeats', 1)
    result[name] = main_header + \
        f'namespace {namespace}\n' + column + endpoint + scalar + audit(['actual_trace', 'scalar_coordinates']) + f'end {namespace}\n'
    return result
