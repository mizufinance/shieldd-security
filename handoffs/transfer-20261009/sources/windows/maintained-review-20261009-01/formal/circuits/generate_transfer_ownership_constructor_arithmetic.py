"""Bounded actual arithmetic trace from constructed rows and written bits.

This does not supply final target assertion rows. Its arbitrary assignment
interface is fed by the owned native constructor, rather than assuming the
actual ownership trace's Boolean rows or desired scalar endpoint.
"""
from . import generate_transfer_ownership_constructor_bits as bits
from . import transfer_ownership_completion as completion
from .generate_hash_round import _signature_audits


def generate(checked,extracted,readonly_lcs=()):
    bits.generate(checked,extracted,readonly_lcs)
    start,count=bits.candidates._chunk(checked,extracted)
    completion.owner.generate_trace_chunk(checked,extracted)
    columns=[checked['derived'][handle][0][0] for handle in checked['bits']]
    if columns!=list(range(columns[0],columns[0]+252)):
        raise completion.relation.RelationError('ownership arithmetic exact252 bit field source')
    chunk=f'RuntimeOwnershipConstructorChunk{start:03d}';trace=f'RuntimeOwnershipTrace{start:03d}'
    name=f'RuntimeOwnershipConstructorArithmetic{start:03d}'
    source=f'''import ShielddSecurity.{chunk}
import ShielddSecurity.{trace}
import ShielddSecurity.ScalarBitFieldSemantics
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
variable {{F : Type}} [Field F]
theorem rows_complete (rho : Nat → F) (nativeBits : Nat → Bool)
    (constructed : Satisfies rho {chunk}.originalRows)
    (written : ∀ index < 252, rho ({columns[0]}+index) = if nativeBits index then 1 else 0) :
    Satisfies rho {trace}.rawRows := by
  intro row member
  rcases List.mem_append.mp member with arithmetic | bitRow
  · change row ∈ {chunk}.originalRows at arithmetic
    exact constructed row arithmetic
  · simp only [{trace}.bitRows,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at bitRow
    rcases bitRow with '''+' | '.join('rfl' for _ in range(2*count))+'\n'
    for index in range(start,start+count):
        for offset in (2*(125-index),2*(125-index)+1):
            source+=f'''    · apply ScalarBitFieldSemantics.field_square rho [({columns[offset]},1)] (nativeBits {offset})
      simpa only [eval,Int.cast_one,one_mul,add_zero] using written {offset} (by decide)
'''
    source+=f'''theorem actual_trace {{F : Type}} [Field F] [CharP F {trace}.modulus]
    (rho : Nat → F) (nativeBits : Nat → Bool) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (constructed : Satisfies rho {chunk}.originalRows)
    (written : ∀ index < 252, rho ({columns[0]}+index) = if nativeBits index then 1 else 0) :
    TransferOwnership.TraceEquations ({trace}.coefficientD : F)
      ({trace}.base rho) ({trace}.twice rho) ({trace}.triple rho)
      ({trace}.input rho) ({trace}.windows rho) :=
  {trace}.actual_trace_equations rho one four (rows_complete rho nativeBits constructed written)
#print axioms rows_complete
#print axioms actual_trace
end ShielddSecurity.{name}
'''
    return name,_signature_audits(source)
