"""Bounded actual write fences for seeded earlier rows, without row truth.

This consumes maintained window/program declarations after their actual row
replay. Every gap result is checked on imported stage writes. The full join
uses eight bounded certificates and symbolic lower-origin frame transport.
"""
import hashlib,re
from .transfer_relation import RelationError
from .generate_transfer_authorization_completion import _body,FIXED_STARTS


def _pair(index):
    name=f'ShielddSecurity.RuntimeFixedSpendWindow{index:03d}Program'
    return f'(({name}.program ((encodeBits 252 n)[{2*index}]?.getD false) ((encodeBits 252 n)[{2*index+1}]?.getD false)),{name}.after)'


def generate(sources):
    programs=[f'RuntimeFixedSpendWindow{index:03d}Program' for index in range(126)]
    full='RuntimeTransferFixedSpendCompletion';order='RuntimeFixedSpendRandomizerOrder'
    if not isinstance(sources,dict) or set(sources)!=set(programs+[full,order]):
        raise RelationError('exact all126 actual prefix frame dependency sources')
    for index,module in enumerate(programs):
        body=_body(module,sources[module])
        if (body.count('def program (low high : Bool) : GroupFixedCircuitCompletion.Program where')!=1 or
                body.count('stages := ShielddSecurity.RuntimeFixedSpendWindow'+f'{index:03d}'+'Completion.completionSteps')!=1):
            raise RelationError('exact maintained actual window program stage declaration')
    body=_body(full,sources[full])
    segments='def segments (n : Nat) : List (GroupFixedCircuitCompletion.Program × GroupFixedCircuitBounds.Frame) := ['+','.join(_pair(index) for index in range(126))+']'
    if body.count(segments)!=1:
        raise RelationError('exact126 ordered source program/frame pairs')
    order_body=_body(order,sources[order])
    if (order_body.count('def allStages : List CompilerCompletion.Step := prefix016')!=1 or
            order_body.count('def prefix000 : List CompilerCompletion.Step := []')!=1 or
            any(order_body.count(f'def chunk{index:03d} : List CompilerCompletion.Step :=')!=1 or
                order_body.count(f'def prefix{index+1:03d} : List CompilerCompletion.Step := prefix{index:03d} ++ chunk{index:03d}')!=1
                for index in range(16))):
        raise RelationError('exact16 ordered comparator chunks')
    modules={}
    for start in FIXED_STARTS:
        indices=list(range(start,min(start+16,126)))
        name=f'RuntimeFixedSpendPrefixGap{start:03d}'
        source='import ShielddSecurity.GroupPrefixFrameTransport\n'+''.join(
            'import ShielddSecurity.'+programs[index]+'\n' for index in indices)
        source+=f'''set_option maxHeartbeats 300000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
def pairs (n : Nat) : List (GroupFixedCircuitCompletion.Program × GroupFixedCircuitBounds.Frame) := ['''+','.join(_pair(index) for index in indices)+']\n'
        for index in indices:
            program=programs[index]
            source+=f'''-- Actual maintained program dependency: {hashlib.sha256(sources[program]).hexdigest()}
private theorem gap{index:03d} (low high : Bool) :
    ∀ stage ∈ ({program}.program low high).stages, ∀ column ∈ stage.writes,
      column < 22738 ∨ 61934 ≤ column := by
  have checked : ({program}.program low high).stages.all (fun stage => stage.writes.all
      (fun column => decide (column < 22738 ∨ 61934 ≤ column))) = true := by
    change ({program}.program false false).stages.all (fun stage => stage.writes.all
      (fun column => decide (column < 22738 ∨ 61934 ≤ column))) = true
    decide
  intro stage member column written
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked stage member) column written)
'''
        source+='''theorem gaps (n : Nat) : ∀ segment ∈ pairs n, ∀ stage ∈ segment.1.stages,
    ∀ column ∈ stage.writes, column < 22738 ∨ 61934 ≤ column := by
  intro segment member
  simp only [pairs,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
  rcases member with '''+' | '.join('rfl' for _ in indices)+'\n'
        source+=''.join(f'  · exact gap{index:03d} _ _\n' for index in indices)
        source+='set_option pp.all true in\n#check @gaps\n#print axioms gaps\nend ShielddSecurity.'+name+'\n'
        modules[name]=source
    name='RuntimeTransferFixedSpendPrefixFrames'
    names=[f'RuntimeFixedSpendPrefixGap{start:03d}' for start in FIXED_STARTS]
    source='import ShielddSecurity.'+full+'\n'+''.join('import ShielddSecurity.'+part+'\n' for part in names)
    source+=f'''set_option maxHeartbeats 300000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
def groups (n : Nat) : List (List (GroupFixedCircuitCompletion.Program × GroupFixedCircuitBounds.Frame)) := ['''+','.join(part+'.pairs n' for part in names)+']\n'
    source+=f'''theorem bounds (n : Nat) : GroupFixedCircuitBounds.Certified 22738 200692
    RuntimeFixedSpendWindow000Program.before ({full}.segments n) := by
  apply GroupPrefixFrameTransport.lower_origin_certified 22738 61934 200692
    RuntimeFixedSpendWindow000Program.before ({full}.segments n) (by decide) ({full}.certified_bounds n)
  have joined : {full}.segments n = (groups n).flatten := rfl
  rw [joined]
  intro segment member
  obtain ⟨part,partMember,segmentMember⟩ := List.mem_flatten.mp member
  simp only [groups,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at partMember
  rcases partMember with '''+' | '.join('rfl' for _ in names)+'\n'
    source+=''.join('  · exact '+part+'.gaps n segment segmentMember\n' for part in names)
    source+='set_option pp.all true in\n#check @bounds\n#print axioms bounds\nend ShielddSecurity.'+name+'\n'
    modules[name]=source
    name='RuntimeFixedSpendRandomizerPrefixWrites'
    source=f'''import ShielddSecurity.{order}
import ShielddSecurity.GroupPrefixFrameTransport
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
def priorFrame : GroupFixedCircuitBounds.Frame := ⟨3767,61934⟩
'''
    for index in range(16):
        source+=f'''private theorem chunk{index:03d} : ∀ column ∈ PoseidonCompletion.writes ({order}.chunk{index:03d}),
    ¬GroupFixedCircuitBounds.covers 22738 200692 priorFrame column := by
  have checked : (PoseidonCompletion.writes ({order}.chunk{index:03d})).all (fun column =>
      decide (¬GroupFixedCircuitBounds.covers 22738 200692 priorFrame column)) = true := by decide
  intro column member
  exact of_decide_eq_true (List.all_eq_true.mp checked column member)
'''
    source+=f'''theorem all_writes : ∀ column ∈ PoseidonCompletion.writes ({order}.allStages),
    ¬GroupFixedCircuitBounds.covers 22738 200692 priorFrame column := by
  intro column member
  simp only [PoseidonCompletion.writes,{order}.allStages,'''+','.join(order+f'.prefix{index:03d}' for index in range(17))+''',
    List.flatMap_append,List.flatMap_nil,List.mem_append,List.not_mem_nil,false_or] at member
  rcases member with '''+' | '.join('inside' for _ in range(16))+'\n'
    source+=''.join(f'  · exact chunk{index:03d} column inside\n' for index in range(16))
    source+='set_option pp.all true in\n#check @all_writes\n#print axioms all_writes\nend ShielddSecurity.'+name+'\n'
    modules[name]=source
    return modules
