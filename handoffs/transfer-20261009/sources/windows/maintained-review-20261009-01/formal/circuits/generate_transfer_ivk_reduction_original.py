"""Original Boolean/materialization row transport, after actual construction.

The33 Data chunks share252 original Boolean rows. Their union, the gate pair
and the seven tail rows covers1275 original physical rows. The inverse's three
rows and independently legal native viewing-key predicate remain separate.
"""
from . import transfer_ivk_reduction_completion as reduction
from . import generate_transfer_ivk_reduction_join as joins
from .generate_hash_round import linear


def _link(copy,qcol,rcol,qs,rs):
    return f'''private theorem copy_link {{F : Type}} [Field F] (codec : TransferReduction.CanonicalField F) (base : Nat → F)
    (linked : base {copy} = base 0) : O.construct codec base {copy} = O.construct codec base 0 := by
  have left := ScalarReductionSupport.kept_column base codec (eval base O.hashValue) {qcol} {rcol} {qs} {rs}
    O.allStages O.kept O.ordered {copy} (by decide) (by decide) (by decide) (by decide)
  have right := ScalarReductionSupport.kept_column base codec (eval base O.hashValue) {qcol} {rcol} {qs} {rs}
    O.allStages O.kept O.ordered 0 (by decide) (by decide) (by decide) (by decide)
  exact left.trans (linked.trans right.symm)
'''


def generate(data,accepted_ivk,extracted,expected_relation,readonly_lcs=()):
    plan=reduction.plan(data,accepted_ivk,extracted,expected_relation,readonly_lcs)
    chunks,offsets=joins._chunks(plan)
    q,r=plan['phases'][:2];qcol,rcol=q['value'][0][0],r['value'][0][0];qs,rs=q['start'],r['start']
    copy=plan['checked']['metadata']['constant_copy'];parts=[];selected=set()
    for phase in plan['phases']:
        for start in range(0,phase['width'],16):
            products=joins._local(plan,chunks,offsets,phase,start)
            index=start//16;stop=min(start+16,phase['width'])
            selected.update(plan['roles'][f'{phase["key"]}.boolean.{i}'] for i in range(start,stop))
            selected.update(row for i in range(max(1,start),stop) for row in phase['stages'][i-1]['rows'])
            d=f'RuntimeTransferIvkComparison{phase["phase"]}DataChunk{index}'
            j=f'RuntimeTransferIvkComparison{phase["phase"]}RowJoinChunk{index}'
            name=f'RuntimeTransferIvkComparison{phase["phase"]}OriginalChunk{index}';parts.append(name)
            source=f'''import ShielddSecurity.{j}
import ShielddSecurity.ScalarReductionSupport
import ShielddSecurity.ScalarTerminalCompletion
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
namespace O := {joins.ORDER}
namespace D := {d}
namespace J := {j}
def rawRows : List Row := D.rawRows
def originalIndices : List Nat := D.originalIndices
{_link(copy,qcol,rcol,qs,rs)}
theorem original_complete {{F : Type}} [Field F] [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (base : Nat → F) (linked : base {copy} = base 0) :
    Satisfies (O.construct codec base) rawRows := by
  have normalized : Satisfies (O.construct codec base) D.rows := by
    intro row member
    exact Compiler.checked_row_sound (O.construct codec base) O.rows row (O.constructs codec base)
      (ScalarChunkComposition.row_check_lift Scalar.modulus J.boundedRows O.rows J.included row
        (List.all_eq_true.mp J.checked_local row member))
  exact ScalarTerminalCompletion.unoutline_complete (O.construct codec base) {copy} D.rawRows
    (copy_link codec base linked) normalized
#print axioms original_complete
end ShielddSecurity.{name}
'''
            yield name,joins._qualify(source,{'O':joins.ORDER,'D':d,'J':j})
    gate=plan['gate_stage'];indices=gate['rows'];selected.update(indices)
    gate_name='RuntimeTransferIvkGateProductOriginal';parts.append(gate_name)
    rows='['+',\n'.join('⟨'+linear(plan['raw'][i][0])+','+linear(plan['raw'][i][1])+'⟩' for i in indices)+']'
    source=f'''import ShielddSecurity.{joins.ORDER}
import ShielddSecurity.ScalarReductionSupport
import ShielddSecurity.ScalarTerminalCompletion
import ShielddSecurity.ScalarChunkComposition
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.{gate_name}
namespace O := {joins.ORDER}
def originalIndices : List Nat := {indices}
def rawRows : List Row := {rows}
def rows : List Row := Compiler.unoutlineRows {copy} rawRows
private theorem gate_included : ∀ row ∈ CompilerCompletion.emitted O.chunk033, row ∈ O.rows := by
{joins._included_product(33)}
theorem checked_local : rows.all (fun row => Compiler.checkRow Scalar.modulus (CompilerCompletion.emitted O.chunk033) row) = true := by decide
{_link(copy,qcol,rcol,qs,rs)}
theorem original_complete {{F : Type}} [Field F] [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (base : Nat → F) (linked : base {copy} = base 0) :
    Satisfies (O.construct codec base) rawRows := by
  have normalized : Satisfies (O.construct codec base) rows := by
    intro row member
    exact Compiler.checked_row_sound (O.construct codec base) O.rows row (O.constructs codec base)
      (ScalarChunkComposition.row_check_lift Scalar.modulus (CompilerCompletion.emitted O.chunk033) O.rows gate_included row
        (List.all_eq_true.mp checked_local row member))
  exact ScalarTerminalCompletion.unoutline_complete (O.construct codec base) {copy} rawRows
    (copy_link codec base linked) normalized
#print axioms checked_local
#print axioms original_complete
end ShielddSecurity.{gate_name}
'''
    yield gate_name,joins._qualify(source,{'O':joins.ORDER})
    tail_roles=['quotient.reconstruction','remainder.reconstruction','quotient_end.assertion',
        'remainder_end.assertion','hash-equation','terminal-gate','constant-copy']
    selected.update(plan['roles'][key] for key in tail_roles)
    if selected!=set(plan['raw'])-set(plan['inverse']['rows']) or len(selected)!=1275:
        raise reduction.relation.RelationError('IVK exact1275 original comparison/gate/tail physical coverage')
    name='RuntimeTransferIvkReductionOriginalRows';tail='RuntimeTransferIvkReductionTailCompletion'
    source=''.join(f'import ShielddSecurity.{part}\n' for part in parts)+f'import ShielddSecurity.{tail}\n'
    source+=f'''set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
namespace O := {joins.ORDER}
namespace T := {tail}
def originalIndices : List Nat := {sorted(selected)}
def parts : List (List Row) := [{','.join(part+'.rawRows' for part in parts)}]
def originalRows : List Row := parts.flatten ++ T.rawRows
theorem original_complete {{F : Type}} [Field F] [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (base : Nat → F) (one : base 0 = 1) (four : (4 : F) ≠ 0)
    (linked : base {copy} = base 0) : Satisfies (O.construct codec base) originalRows := by
  have blocks : ∀ part ∈ parts, Satisfies (O.construct codec base) part := by
    intro part member
    simp only [parts,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with {' | '.join('rfl' for _ in parts)}
'''
    for part in parts:source+=f'    · exact {part}.original_complete codec base linked\n'
    source+='''  intro row member
  rcases List.mem_append.mp member with materialization | assertion
  · obtain ⟨part,present,found⟩ := List.mem_flatten.mp materialization
    exact blocks part present row found
  · exact T.original_complete codec base one four linked row assertion
#print axioms original_complete
'''
    yield name,joins._qualify(source+f'end ShielddSecurity.{name}\n',{'O':joins.ORDER,'T':tail})
