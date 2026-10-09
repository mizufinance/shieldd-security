"""Bounded actual comparison certificates for the shared reduction assignment.

The remainder and terminal modules refer to the SAME252 physical Boolean
rows. They never reassign a terminal bit block or promise an endpoint value.
The source-owned Euclidean seed/constructor and finite row inclusion joins
must establish common-row satisfaction before these certificates are used.
"""
from . import transfer_ivk_reduction_completion as reduction
from .generate_hash_round import linear,_signature_audits


def generate(data,accepted_ivk,extracted,expected_relation,readonly_lcs=()):
    plan=reduction.plan(data,accepted_ivk,extracted,expected_relation,readonly_lcs)
    copy=plan['checked']['metadata']['constant_copy']
    for phase in plan['phases']:
        for chunk,start in enumerate(range(0,phase['width'],16)):
            stop=min(start+16,phase['width']);indices=[];steps=[]
            for index in range(start,stop):
                bit_role=f'{phase["key"]}.boolean.{index}'
                indices.append(plan['roles'][bit_role])
                step=phase['steps'][index]
                if index:
                    stage=phase['stages'][index-1];indices.extend(stage['rows'])
                    certificate='.product '+linear([(stage['auxiliary'],1)])
                else:certificate='.foldedLeft 1'
                steps.append('⟨'+','.join((linear(step['before']),linear(step['left']),linear(step['after']),
                    'true' if step['right'] else 'false',linear(step['factor']),linear(step['product']),certificate))+'⟩')
            if len(indices)!=len(set(indices)):
                raise reduction.relation.RelationError('IVK bounded comparison data row reuse')
            name=f'RuntimeTransferIvkComparison{phase["phase"]}DataChunk{chunk}'
            rows='['+',\n'.join('⟨'+linear(plan['raw'][i][0])+','+linear(plan['raw'][i][1])+'⟩' for i in indices)+']'
            maximum=sum(phase['steps'][i]['right']*(2**(i-start)) for i in range(start,stop))
            source=f'''import ShielddSecurity.ScalarChunkComposition
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
def modulus : Nat := {reduction.relation.MODULUS}
def originalIndices : List Nat := {indices}
def rawRows : List Row := {rows}
def rows : List Row := Compiler.unoutlineRows {copy} rawRows
def initial : Linear := {linear(phase['steps'][start]['before'])}
def final : Linear := {linear(phase['steps'][stop-1]['after'])}
def steps : List ScalarRows.StepData := [{','.join(steps)}]
theorem checked_chain : ScalarRows.checkChain modulus rows initial steps = true := by decide
theorem checked_bits : ScalarBits.checkBits modulus rows (steps.map ScalarRows.StepData.left) = true := by decide
theorem endpoint_exact (before : Linear) : ScalarComparisonBounds.endpoint before steps = final := rfl
theorem right_value : binary (steps.map ScalarRows.StepData.right) = {maximum} := by decide
'''
            for export in ('checked_chain','checked_bits','endpoint_exact','right_value'):
                source+='#print axioms '+export+'\n'
            yield name,_signature_audits(source+f'end ShielddSecurity.{name}\n')
