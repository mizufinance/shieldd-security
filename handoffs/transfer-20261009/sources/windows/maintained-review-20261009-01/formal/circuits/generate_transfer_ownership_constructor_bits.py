"""Bounded actual program-bit adapters for written native IVK field values."""
from . import generate_transfer_ownership_constructor_candidates as candidates
from . import transfer_ownership_completion as completion
from .generate_hash_round import _signature_audits


def generate(checked,extracted,readonly_lcs=()):
    start,count=candidates._chunk(checked,extracted)
    if checked['metadata'].get('schema')!='shieldd-transfer-ownership-v1' or len(checked['bits'])!=252:
        raise completion.relation.RelationError('ownership exact owned252 source-bit family')
    observed=[checked['derived'][handle] for handle in checked['bits']]
    if len(observed[0])!=1 or observed[0][0][1]!=1:
        raise completion.relation.RelationError('ownership actual first bit singleton')
    bit_start=observed[0][0][0]
    if observed!=[completion.canonical([(bit_start+index,1)]) for index in range(252)]:
        raise completion.relation.RelationError('ownership actual sequential singleton252 bit columns')
    for offset in range(count):
        completion.window_plan(checked,extracted,offset,False,readonly_lcs)
    chunk=f'RuntimeOwnershipConstructorChunk{start:03d}'
    programs=[f'RuntimeOwnershipWindow{start+offset:03d}Program' for offset in range(count)]
    name=f'RuntimeOwnershipConstructorBits{start:03d}'
    source=f'''import ShielddSecurity.{chunk}
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
open GroupFixedCircuitCompletion
theorem field_values {{F : Type}} [Field F] (base : Nat → F) (bits : Nat → Bool)
    (written : ∀ index < 252, base ({bit_start}+index) = (if bits index then 1 else 0)) :
    ∀ program ∈ {chunk}.programs bits,
      eval base program.low = (if program.lowBit then 1 else 0) ∧
      eval base program.high = (if program.highBit then 1 else 0) := by
  intro program member
  simp only [{chunk}.programs,{chunk}.segments,List.map_cons,List.map_nil,
    List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with '''+' | '.join('rfl' for _ in programs)+'\n'
    for offset,program in enumerate(programs):
        low=2*(125-start-offset);high=low+1
        source+=f'''  · constructor
    · change eval base [({bit_start+low},1)] = (if bits {low} then 1 else 0)
      simpa only [eval,Int.cast_one,one_mul,add_zero] using written {low} (by decide)
    · change eval base [({bit_start+high},1)] = (if bits {high} then 1 else 0)
      simpa only [eval,Int.cast_one,one_mul,add_zero] using written {high} (by decide)
'''
    source+='#print axioms field_values\n'
    return name,_signature_audits(source+f'end ShielddSecurity.{name}\n')
