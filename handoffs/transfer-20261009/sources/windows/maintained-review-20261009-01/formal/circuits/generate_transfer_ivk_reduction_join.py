"""Bounded comparator certificates for one constructed IVK assignment.

This emitter consumes the same strictly reaccepted reduction plan as the Data
and Order emitters. It joins only rows already retained by the prefix replay;
it never scans another stream or assumes an endpoint/assertion value.
"""
from . import transfer_ivk_reduction_completion as reduction
from .transfer_balance_rows import canonical,combine
from .generate_hash_round import linear,_signature_audits
import re

ORDER='RuntimeTransferIvkReductionProductOrder'


def _qualify(source,aliases):
    # Lean namespace prefixes are fully qualified; Python aliases are only a
    # renderer convenience and introduce no generated namespace commands.
    for alias,target in aliases.items():
        source=source.replace(f'namespace {alias} := {target}\n','')
        source=re.sub(r'\b'+re.escape(alias)+r'\.',target+'.',source)
    return _signature_audits(source)


def _chunks(plan):
    result=[];offsets=[]
    for phase in plan['phases']:
        offsets.append(len(result))
        result.extend(phase['stages'][i:i+16] for i in range(0,len(phase['stages']),16))
    result.append([plan['gate_stage']])
    if len(result)!=34 or sum(map(len,result))!=506 or max(map(len,result))>16:
        raise reduction.relation.RelationError('IVK exact bounded product chunk inventory')
    return result,offsets


def _stage_rows(stage):
    return ((combine(stage['left'],stage['right'],-1),((stage['auxiliary'],1),)),
        (combine(stage['left'],stage['right']),
         combine(((stage['auxiliary'],1),),combine(stage['remainder'],((stage['output'],1),)),4)))


def _local(plan,chunks,offsets,phase,start):
    stop=min(start+16,phase['width']);index=start//16
    products=[offsets[phase['phase']]+index]
    if index:products.insert(0,products[0]-1)
    expected={(((phase['start']+i,1),),((phase['start']+i,1),)) for i in range(start,stop)}
    for product in products:
        for stage in chunks[product]:expected.update(_stage_rows(stage))
    copy=plan['checked']['metadata']['constant_copy']
    raw=[]
    for i in range(start,stop):
        raw.append(plan['raw'][plan['roles'][f'{phase["key"]}.boolean.{i}']])
        if i:raw.extend(plan['raw'][row] for row in phase['stages'][i-1]['rows'])
    for a,b in raw:
        unoutline=lambda terms:canonical((0 if c==copy else c,v) for c,v in terms)
        if (unoutline(a),unoutline(b)) not in expected:
            raise reduction.relation.RelationError('IVK bounded Data canonical row coverage')
    return products


def _included_product(index):
    # Traverse only34 symbolic append nodes; do not unfold any product body.
    lines=['  intro row member','  apply List.mem_append_right O.initialRows',
           '  change row ∈ CompilerCompletion.emitted O.prefix034']
    for current in range(34,index+1,-1):
        lines.extend((f'  rw [O.prefix{current:03d},ScalarRandomizerBounds.emitted_append]',
                      '  apply List.mem_append_left'))
    lines.extend((f'  rw [O.prefix{index+1:03d},ScalarRandomizerBounds.emitted_append]',
                  '  exact List.mem_append_right _ member'))
    return '\n'.join(lines)


def _bounded(plan,chunks,offsets,phase,start):
    number=start//16;stop=min(start+16,phase['width'])
    products=_local(plan,chunks,offsets,phase,start)
    data=f'RuntimeTransferIvkComparison{phase["phase"]}DataChunk{number}'
    name=f'RuntimeTransferIvkComparison{phase["phase"]}RowJoinChunk{number}'
    q,r=plan['phases'][:2]
    body='bitRows'+''.join(f' ++ CompilerCompletion.emitted O.chunk{i:03d}' for i in products)
    source=f'''import ShielddSecurity.{ORDER}
import ShielddSecurity.{data}
import ShielddSecurity.ScalarRowTransport
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
namespace O := {ORDER}
namespace D := {data}
def bitRows : List Row := (List.range' {phase['start']+start} {stop-start}).map booleanRow
def boundedRows : List Row := {body}
theorem checked_local : D.rows.all (fun actual => Compiler.checkRow Scalar.modulus boundedRows actual) = true := by decide
private theorem bit_included : ∀ row ∈ bitRows, row ∈ O.rows := by
  intro row member
  obtain ⟨column,present,rfl⟩ := List.mem_map.mp member
  have checked : (List.range' {phase['start']+start} {stop-start}).all
    (fun column => decide (column ∈ List.range' {phase['start']} {phase['width']})) = true := by decide
  have original := of_decide_eq_true (List.all_eq_true.mp checked column present)
  apply List.mem_append_left (CompilerCompletion.emitted O.allStages)
  change booleanRow column ∈
    ScalarComparatorCompletion.initialRows {q['value'][0][0]} {q['start']} 4 ++
    ScalarComparatorCompletion.initialRows {r['value'][0][0]} {r['start']} 252
'''
    source+=('  apply List.mem_append_left\n' if phase['phase']==0 else '  apply List.mem_append_right\n')
    source+='  exact List.mem_append_left _ (List.mem_map.mpr ⟨column,original,rfl⟩)\n'
    for i in products:
        source+=f'private theorem product_included{i:03d} : ∀ row ∈ CompilerCompletion.emitted O.chunk{i:03d}, row ∈ O.rows := by\n'+_included_product(i)+'\n'
    source+='theorem included : ∀ row ∈ boundedRows, row ∈ O.rows := by\n  intro row member\n  simp only [boundedRows,List.mem_append] at member\n'
    if len(products)==1:
        source+=f'  rcases member with bit | product\n  · exact bit_included row bit\n  · exact product_included{products[0]:03d} row product\n'
    else:
        source+=f'  rcases member with (bit | previous) | current\n  · exact bit_included row bit\n  · exact product_included{products[0]:03d} row previous\n  · exact product_included{products[1]:03d} row current\n'
    source+='''private theorem transported : ∀ actual ∈ D.rows, Compiler.checkRow Scalar.modulus O.rows actual = true := by
  intro actual member
  exact ScalarChunkComposition.row_check_lift Scalar.modulus boundedRows O.rows included actual
    (List.all_eq_true.mp checked_local actual member)
theorem chain : ScalarRows.checkChain Scalar.modulus O.rows D.initial D.steps = true :=
  ScalarRowTransport.chain Scalar.modulus D.rows O.rows transported D.initial D.steps D.checked_chain
theorem bits : ScalarBits.checkBits Scalar.modulus O.rows (D.steps.map ScalarRows.StepData.left) = true :=
  ScalarRowTransport.bits Scalar.modulus D.rows O.rows transported _ D.checked_bits
'''
    for export in ('checked_local','included','chain','bits'):source+='#print axioms '+export+'\n'
    return name,_qualify(source+f'end ShielddSecurity.{name}\n',{'O':ORDER,'D':data})


def _phase(phase):
    count=(phase['width']+15)//16;index=phase['phase']
    names=[f'RuntimeTransferIvkComparison{index}DataChunk{i}' for i in range(count)]
    joins=[f'RuntimeTransferIvkComparison{index}RowJoinChunk{i}' for i in range(count)]
    name=f'RuntimeTransferIvkComparison{index}Common'
    source=''.join(f'import ShielddSecurity.{j}\n' for j in joins)
    source+=f'''import ShielddSecurity.TransferReduction
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
namespace O := {ORDER}
'''
    for i,(d,j) in enumerate(zip(names,joins)):
        source+=f'namespace D{i} := {d}\nnamespace J{i} := {j}\n'
    source+='def chunks : List (List ScalarRows.StepData) := ['+','.join(f'D{i}.steps' for i in range(count))+']\n'
    source+='def steps : List ScalarRows.StepData := chunks.flatten\n'
    source+='def bitChunks : List (List Linear) := ['+','.join(f'D{i}.steps.map ScalarRows.StepData.left' for i in range(count))+']\n'
    source+='theorem checked_chunks : ScalarChunkComposition.checkChunks Scalar.modulus O.rows [(0,1)] chunks = true := by\n'
    # Rewriting an endpoint uses the separately audited bounded endpoint lemma.
    source+='  simp only [chunks,ScalarChunkComposition.checkChunks,Bool.and_eq_true]\n'
    for i in range(count):
        source+=('  constructor\n' if i<count else '')
        source+=f'  · exact J{i}.chain\n'
        if i<count-1:source+=f'  rw [D{i}.endpoint_exact]\n'
    source+='  exact True.intro\n'
    source+='''theorem chain : ScalarRows.checkChain Scalar.modulus O.rows [(0,1)] steps = true :=
  ScalarChunkComposition.chunks_certificate Scalar.modulus O.rows [(0,1)] chunks checked_chunks
theorem bits : ScalarBits.checkBits Scalar.modulus O.rows (steps.map ScalarRows.StepData.left) = true := by
  have checked : ScalarChunkComposition.checkBitChunks Scalar.modulus O.rows bitChunks = true := by
    simp only [bitChunks,ScalarChunkComposition.checkBitChunks,Bool.and_eq_true]
'''
    source+='    exact '+''.join(f'⟨J{i}.bits,' for i in range(count))+'True.intro'+('⟩'*count)+'\n'
    source+='  simpa only [steps,chunks,bitChunks,List.flatten_cons,List.flatten_nil,List.map_append,List.map_nil,List.append_nil] using\n    ScalarChunkComposition.bit_chunks_certificate Scalar.modulus O.rows bitChunks checked\n'
    source+=f'''theorem bit_order : steps.map ScalarRows.StepData.left =
    (List.range' {phase['start']} {phase['width']}).map (fun column => [(column,1)]) := by decide
theorem endpoint_final : ScalarComparisonBounds.endpoint [(0,1)] steps = D{count-1}.final := by
'''
    source+='  unfold steps chunks\n  simp only [List.flatten_cons,List.flatten_nil,List.append_nil]\n'
    source+='  rw ['+','.join(['TransferReduction.endpoint_append']*(count-1))+']\n' if count>1 else ''
    source+='  rw ['+','.join(f'D{i}.endpoint_exact' for i in range(count))+']\n'
    maximum=sum(step['right']*(2**i) for i,step in enumerate(phase['steps']))
    source+=f'theorem maximum : binary (steps.map ScalarRows.StepData.right) = {maximum} := by decide\n'
    for export in ('checked_chunks','chain','bits','bit_order','endpoint_final','maximum'):
        source+='#print axioms '+export+'\n'
    return name,_qualify(source+f'end ShielddSecurity.{name}\n',
        {'O':ORDER,**{f'D{i}':d for i,d in enumerate(names)},**{f'J{i}':j for i,j in enumerate(joins)}})


def _endpoints(plan):
    q,r=plan['phases'][:2];qcol,rcol=q['value'][0][0],r['value'][0][0]
    qs,rs=q['start'],r['start'];copy=plan['checked']['metadata']['constant_copy']
    gate=plan['gate_stage'];name='RuntimeTransferIvkReductionEndpoints'
    source=''.join(f'import ShielddSecurity.RuntimeTransferIvkComparison{i}Common\n' for i in range(3))
    source+=f'''import ShielddSecurity.ScalarReductionSupport
import ShielddSecurity.ScalarReductionAssertions
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
namespace O := {ORDER}
namespace Q := RuntimeTransferIvkComparison0Common
namespace R := RuntimeTransferIvkComparison1Common
namespace T := RuntimeTransferIvkComparison2Common
def seeded {{F : Type}} [Field F] (codec : TransferReduction.CanonicalField F) (base : Nat → F) : Nat → F :=
  ScalarReductionSeed.seed base codec (eval base O.hashValue) {qcol} {rcol}
def qBitsBase {{F : Type}} [Field F] (codec : TransferReduction.CanonicalField F) (base : Nat → F) : Nat → F :=
  writeBits (seeded codec base) {qs} (encodeBits 4 (ScalarReductionSeed.quotient codec (eval base O.hashValue)))
theorem written_quotient_bits {{F : Type}} [Field F] (codec : TransferReduction.CanonicalField F) (base : Nat → F) :
    ∀ column ∈ List.range' {qs} 4, O.construct codec base column =
      writeBits (seeded codec base) {qs} (encodeBits 4 (ScalarReductionSeed.quotient codec (eval base O.hashValue))) column :=
  ScalarReductionSupport.written_quotient_bits base codec (eval base O.hashValue) {qcol} {rcol} {qs} {rs}
    O.allStages O.kept O.ordered (by intro column member; exact Or.inl (by have := List.mem_range'.mp member; omega))
theorem written_remainder_bits {{F : Type}} [Field F] (codec : TransferReduction.CanonicalField F) (base : Nat → F) :
    ∀ column ∈ List.range' {rs} 252, O.construct codec base column =
      writeBits (qBitsBase codec base) {rs} (encodeBits 252 (ScalarReductionSeed.remainder codec (eval base O.hashValue))) column :=
  ScalarReductionSupport.written_remainder_bits base codec (eval base O.hashValue) {qcol} {rcol} {qs} {rs}
    O.allStages O.kept O.ordered
private theorem kept_zero {{F : Type}} [Field F] (codec : TransferReduction.CanonicalField F) (base : Nat → F) :
    O.construct codec base 0 = base 0 :=
  ScalarReductionSupport.kept_column base codec (eval base O.hashValue) {qcol} {rcol} {qs} {rs}
    O.allStages O.kept O.ordered 0 (by decide) (by decide) (by decide) (by decide)
theorem constant_one {{F : Type}} [Field F] (codec : TransferReduction.CanonicalField F) (base : Nat → F)
    (one : base 0 = 1) : O.construct codec base 0 = 1 := (kept_zero codec base).trans one
'''
    for phase,alias,which,width,start,fallback in (
        (q,'Q','quotient',4,qs,'seeded'),(r,'R','remainder',252,rs,'qBitsBase')):
        maximum=sum(step['right']*(2**i) for i,step in enumerate(phase['steps']))
        operand_bound=('≤ 8' if width==4 else '< Scalar.order')
        bound_projection='1' if width==4 else '2.1'
        proof='by omega' if width==4 else \
            'operandBound.trans (by decide : Scalar.order < 2^252)'
        le='operandBound' if width==4 else \
            'by\n    change ScalarReductionSeed.remainder codec (eval base O.hashValue) ≤ Scalar.order-1\n    omega'
        source+=f'''theorem {which}_endpoint {{F : Type}} [Field F] [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (base : Nat → F) (one : base 0 = 1) (four : (4 : F) ≠ 0) :
    eval (O.construct codec base) (ScalarComparisonBounds.endpoint [(0,1)] {alias}.steps) = 1 := by
  have operandBound : ScalarReductionSeed.{which} codec (eval base O.hashValue) {operand_bound} :=
    (ScalarReductionCompletion.decoded_operands codec (eval base O.hashValue)).{bound_projection}
  have small : ScalarReductionSeed.{which} codec (eval base O.hashValue) < 2^{width} := {proof}
  have bounded : ScalarReductionSeed.{which} codec (eval base O.hashValue) ≤ {maximum} := {le}
  have result := ScalarConstructedBits.comparison_from_written_bits ({fallback} codec base) (O.construct codec base) {start}
    (encodeBits {width} (ScalarReductionSeed.{which} codec (eval base O.hashValue))) O.rows {alias}.steps
    (O.constructs codec base) (constant_one codec base one) four
    (by simpa only [encodeBits_length] using {alias}.bit_order)
    (by simpa only [encodeBits_length] using written_{which}_bits codec base) {alias}.bits {alias}.chain
  simpa only [encodeBits_value {width} _ small,{alias}.maximum,if_pos bounded] using result.2
'''
    source+=f'''theorem terminal_endpoint {{F : Type}} [Field F] [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (base : Nat → F) (one : base 0 = 1) (four : (4 : F) ≠ 0) :
    eval (O.construct codec base) (ScalarComparisonBounds.endpoint [(0,1)] T.steps) =
      (if ScalarReductionSeed.remainder codec (eval base O.hashValue) ≤ Scalar.lastRemainder then 1 else 0) :=
  ScalarReductionAssertions.terminal_endpoint (qBitsBase codec base) (O.construct codec base) codec (eval base O.hashValue)
    {rs} O.rows T.steps (O.constructs codec base) (constant_one codec base one) four T.bit_order
    (written_remainder_bits codec base) T.bits T.chain T.maximum
private theorem gate_included : ∀ row ∈ CompilerCompletion.emitted O.chunk033, row ∈ O.rows := by
{_included_product(33)}
def gate : Linear := {linear([(gate['output'],1)])}
def gateProduct : ScalarRows.ProductData := .product {linear([(gate['auxiliary'],1)])}
private theorem checked_gate : ScalarRows.checkProduct Scalar.modulus O.rows [({qs+3},1)]
    (Compiler.subtract [(0,1)] (ScalarComparisonBounds.endpoint [(0,1)] T.steps)) gate gateProduct = true := by
  rw [T.endpoint_final]
  exact ScalarChunkComposition.product_check_lift Scalar.modulus (CompilerCompletion.emitted O.chunk033) O.rows
    gate_included _ _ gate gateProduct (by decide)
theorem gate_zero {{F : Type}} [Field F] [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (base : Nat → F) (one : base 0 = 1) (four : (4 : F) ≠ 0) :
    eval (O.construct codec base) gate = 0 := by
  have high : O.construct codec base ({qs}+3) = writeBits (qBitsBase codec base) {qs}
      (encodeBits 4 (ScalarReductionSeed.quotient codec (eval base O.hashValue))) ({qs}+3) := by
    have written := written_quotient_bits codec base ({qs}+3) (by decide)
    rw [written]
    simp only [writeBits,encodeBits_length,if_pos (show {qs} ≤ {qs}+3 ∧ {qs}+3 < {qs}+4 from by decide)]
  exact ScalarReductionAssertions.gate_zero (qBitsBase codec base) (O.construct codec base) codec (eval base O.hashValue)
    {qs} {rs} O.rows T.steps (O.constructs codec base) (constant_one codec base one) four high T.bit_order
    (written_remainder_bits codec base) T.bits T.chain T.maximum gate gateProduct checked_gate
theorem operands {{F : Type}} [Field F] (codec : TransferReduction.CanonicalField F) (base : Nat → F) :
    O.construct codec base {qcol} = (ScalarReductionSeed.quotient codec (eval base O.hashValue) : F) ∧
    O.construct codec base {rcol} = (ScalarReductionSeed.remainder codec (eval base O.hashValue) : F) := by
  have initial := ScalarReductionSeed.seed_operands base codec (eval base O.hashValue) {qcol} {rcol} (by decide)
  have qKept := CompilerCompletion.run_preserves
    (ScalarReductionSeed.bitBase base codec (eval base O.hashValue) {qcol} {rcol} {qs} {rs})
    O.allStages O.kept O.initialRows O.ordered {qcol} (by decide)
  have rKept := CompilerCompletion.run_preserves
    (ScalarReductionSeed.bitBase base codec (eval base O.hashValue) {qcol} {rcol} {qs} {rs})
    O.allStages O.kept O.initialRows O.ordered {rcol} (by decide)
  have qInitial : ScalarReductionSeed.bitBase base codec (eval base O.hashValue) {qcol} {rcol} {qs} {rs} {qcol} =
      ScalarReductionSeed.seed base codec (eval base O.hashValue) {qcol} {rcol} {qcol} := by
    rw [ScalarReductionSeed.bitBase,writeBits_preserves _ {rs} _ {qcol} (by simp only [encodeBits_length]; decide),
      writeBits_preserves _ {qs} _ {qcol} (by simp only [encodeBits_length]; decide)]
  have rInitial : ScalarReductionSeed.bitBase base codec (eval base O.hashValue) {qcol} {rcol} {qs} {rs} {rcol} =
      ScalarReductionSeed.seed base codec (eval base O.hashValue) {qcol} {rcol} {rcol} := by
    rw [ScalarReductionSeed.bitBase,writeBits_preserves _ {rs} _ {rcol} (by simp only [encodeBits_length]; decide),
      writeBits_preserves _ {qs} _ {rcol} (by simp only [encodeBits_length]; decide)]
  exact ⟨qKept.trans (qInitial.trans initial.1),rKept.trans (rInitial.trans initial.2.1)⟩
theorem hash_equation {{F : Type}} [Field F] (codec : TransferReduction.CanonicalField F) (base : Nat → F) :
    O.construct codec base {qcol} * (Scalar.order : F) + O.construct codec base {rcol} =
      eval (O.construct codec base) O.hashValue := by
  have unchanged := ScalarReductionSupport.hash_preserved base codec (eval base O.hashValue) {qcol} {rcol} {qs} {rs}
    O.allStages O.kept O.ordered O.hashValue (by
      have checked : O.hashValue.all (fun term => decide (term.1 ∈ O.kept ∧ term.1 ∉ [{qcol},{rcol}] ∧
        (term.1 < {qs} ∨ {qs+4} ≤ term.1) ∧ (term.1 < {rs} ∨ {rs+252} ≤ term.1))) = true := by decide
      intro term member; exact of_decide_eq_true (List.all_eq_true.mp checked term member))
  change eval (O.construct codec base) O.hashValue = eval base O.hashValue at unchanged
  rw [unchanged,(operands codec base).1,(operands codec base).2]
  exact (ScalarReductionCompletion.decoded_operands codec (eval base O.hashValue)).2.2.2
theorem copy_link {{F : Type}} [Field F] (codec : TransferReduction.CanonicalField F) (base : Nat → F)
    (linked : base {copy} = base 0) : O.construct codec base {copy} = O.construct codec base 0 := by
  rw [kept_zero]
  exact (ScalarReductionSupport.kept_column base codec (eval base O.hashValue) {qcol} {rcol} {qs} {rs}
    O.allStages O.kept O.ordered {copy} (by decide) (by decide) (by decide) (by decide)).trans linked
'''
    for export in ('written_quotient_bits','written_remainder_bits','constant_one','quotient_endpoint','remainder_endpoint',
                   'terminal_endpoint','gate_zero','operands','hash_equation','copy_link'):
        source+='#print axioms '+export+'\n'
    return name,_qualify(source+f'end ShielddSecurity.{name}\n',{'O':ORDER,
        'Q':'RuntimeTransferIvkComparison0Common','R':'RuntimeTransferIvkComparison1Common','T':'RuntimeTransferIvkComparison2Common'})


def _tail(plan):
    name='RuntimeTransferIvkReductionTailCompletion';copy=plan['checked']['metadata']['constant_copy']
    q,r=plan['phases'][:2];qcol,rcol=q['value'][0][0],r['value'][0][0]
    qs,rs=q['start'],r['start']
    roles=['quotient.reconstruction','remainder.reconstruction','quotient_end.assertion',
           'remainder_end.assertion','hash-equation','terminal-gate','constant-copy']
    indices=[plan['roles'][key] for key in roles]
    rows='['+',\n'.join('⟨'+linear(plan['raw'][i][0])+','+linear(plan['raw'][i][1])+'⟩' for i in indices)+']'
    expected=[f'reconstructionRow {qcol} (List.range\' {qs} 4)',f'reconstructionRow {rcol} (List.range\' {rs} 252)',
        '⟨Compiler.subtract '+linear(q['steps'][-1]['after'])+' [(0,1)],[]⟩',
        '⟨Compiler.subtract '+linear(r['steps'][-1]['after'])+' [(0,1)],[]⟩',
        f'⟨Compiler.subtract (scaleLinear (Scalar.order : Int) [({qcol},1)] ++ [({rcol},1)]) O.hashValue,[]⟩',
        '⟨E.gate,[]⟩','⟨[],[]⟩']
    coverage='  intro actual member\n  simp only [rawRows,List.mem_cons,List.not_mem_nil,or_false] at member\n'
    coverage+='  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl\n'
    for i,target in enumerate(expected):
        present='List.mem_cons_self'
        for _ in range(i):present=f'(List.mem_cons_of_mem _ {present})'
        coverage+=f'  · refine ⟨{target},(by exact {present}),?_⟩\n'
        if i<2:
            phase=(q,r)[i]
            target_lc=((phase['value'][0][0],reduction.relation.MODULUS-1),)+tuple(
                (phase['start']+bit,2**bit) for bit in range(phase['width']))
            a,b=plan['raw'][indices[i]]
            normalized=canonical((0 if c==copy else c,v) for c,v in a)
            sign=1 if normalized==canonical(target_lc) else -1
            if normalized!=canonical((c,sign*v) for c,v in target_lc) or b:
                raise reduction.relation.RelationError('IVK original reconstruction exact syntax')
            # Actual sorted singletons already have the symbolic weighted LC
            # syntax. Avoid canonically sorting a253-term LC seven times.
            coverage+='    constructor\n'+('    · left\n' if sign==1 else '    · right\n')
            coverage+='      exact congrArg (Compiler.canonical Scalar.modulus) (by rfl)\n    · rfl\n'
        else:coverage+='    decide\n'
    source=f'''import ShielddSecurity.RuntimeTransferIvkReductionEndpoints
import ShielddSecurity.CompilerSignedCompletion
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
namespace O := {ORDER}
namespace E := RuntimeTransferIvkReductionEndpoints
namespace Q := RuntimeTransferIvkComparison0Common
namespace R := RuntimeTransferIvkComparison1Common
def originalIndices : List Nat := {indices}
def rawRows : List Row := {rows}
def expectedRows : List Row := [
  reconstructionRow {qcol} (List.range' {qs} 4),
  reconstructionRow {rcol} (List.range' {rs} 252),
  ⟨Compiler.subtract {linear(q['steps'][-1]['after'])} [(0,1)],[]⟩,
  ⟨Compiler.subtract {linear(r['steps'][-1]['after'])} [(0,1)],[]⟩,
  ⟨Compiler.subtract (scaleLinear (Scalar.order : Int) [({qcol},1)] ++ [({rcol},1)]) O.hashValue,[]⟩,
  ⟨E.gate,[]⟩,
  ⟨[],[]⟩]
theorem coverage : ∀ actual ∈ rawRows, ∃ expected ∈ expectedRows,
    (Compiler.canonical Scalar.modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical Scalar.modulus expected.a ∨
      Compiler.canonical Scalar.modulus (Compiler.unoutline {copy} actual.a) =
        Compiler.canonical Scalar.modulus (scaleLinear (-1) expected.a)) ∧
    Compiler.canonical Scalar.modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical Scalar.modulus expected.b := by
{coverage}
theorem expected_complete {{F : Type}} [Field F] [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (base : Nat → F) (one : base 0 = 1) (four : (4 : F) ≠ 0)
    (linked : base {copy} = base 0) : Satisfies (O.construct codec base) expectedRows := by
  have qEndpoint := E.quotient_endpoint codec base one four
  have rEndpoint := E.remainder_endpoint codec base one four
  rw [Q.endpoint_final] at qEndpoint
  rw [R.endpoint_final] at rEndpoint
  change eval (O.construct codec base) {linear(q['steps'][-1]['after'])} = 1 at qEndpoint
  change eval (O.construct codec base) {linear(r['steps'][-1]['after'])} = 1 at rEndpoint
  have original := O.constructs codec base
  intro row member
  simp only [expectedRows,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply original
    apply List.mem_append_left (CompilerCompletion.emitted O.allStages)
    apply List.mem_append_left (ScalarComparatorCompletion.initialRows {rcol} {rs} 252)
    exact List.mem_append_right _ (by simp)
  · apply original
    apply List.mem_append_left (CompilerCompletion.emitted O.allStages)
    apply List.mem_append_right (ScalarComparatorCompletion.initialRows {qcol} {qs} 4)
    exact List.mem_append_right _ (by simp)
  · change Square (eval (O.construct codec base) (Compiler.subtract _ [(0,1)])) 0
    rw [Compiler.eval_subtract,qEndpoint]
    simp [eval,E.constant_one codec base one,Square]
  · change Square (eval (O.construct codec base) (Compiler.subtract _ [(0,1)])) 0
    rw [Compiler.eval_subtract,rEndpoint]
    simp [eval,E.constant_one codec base one,Square]
  · simp only [Square,Compiler.eval_subtract,eval_append,eval_scale,eval,Int.cast_one,one_mul,add_zero,
      Int.cast_natCast,Int.cast_ofNat]
    have equation := E.hash_equation codec base
    rw [mul_comm] at equation
    rw [equation]
    simp
  · change Square (eval (O.construct codec base) E.gate) 0
    rw [E.gate_zero codec base one four]
    simp [Square]
  · simp [Square,eval]
theorem original_complete {{F : Type}} [Field F] [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (base : Nat → F) (one : base 0 = 1) (four : (4 : F) ≠ 0)
    (linked : base {copy} = base 0) : Satisfies (O.construct codec base) rawRows :=
  CompilerSignedCompletion.original_rows (O.construct codec base) expectedRows rawRows {copy}
    (E.copy_link codec base linked) (expected_complete codec base one four linked) coverage
'''
    for export in ('coverage','expected_complete','original_complete'):source+='#print axioms '+export+'\n'
    return name,_qualify(source+f'end ShielddSecurity.{name}\n',{'O':ORDER,'E':'RuntimeTransferIvkReductionEndpoints',
        'Q':'RuntimeTransferIvkComparison0Common','R':'RuntimeTransferIvkComparison1Common'})


def generate(data,accepted_ivk,extracted,expected_relation,readonly_lcs=()):
    plan=reduction.plan(data,accepted_ivk,extracted,expected_relation,readonly_lcs)
    chunks,offsets=_chunks(plan)
    for phase in plan['phases']:
        for start in range(0,phase['width'],16):yield _bounded(plan,chunks,offsets,phase,start)
        yield _phase(phase)
    yield _endpoints(plan)
    yield _tail(plan)
