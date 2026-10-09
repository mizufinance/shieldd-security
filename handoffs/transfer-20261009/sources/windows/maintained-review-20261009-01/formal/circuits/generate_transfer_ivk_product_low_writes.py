"""Symbolic low-column exclusion from the existing 34 allocation certificates."""
import re


def generate(product_order_source):
    bounds = re.findall(
        r'theorem checked_bound(\d{3}) : ScalarRandomizerBounds.checkBounded '
        r'(\d+) (\d+) chunk\1 = true', product_order_source)
    assert [index for index, _, _ in bounds] == [f'{i:03d}' for i in range(34)]
    assert all(50200 <= int(lower) <= int(upper) for _, lower, upper in bounds)
    assert 'def allStages : List CompilerCompletion.Step := prefix034' in product_order_source
    name = 'RuntimeIvkReductionLowWrites'
    order = 'RuntimeTransferIvkReductionProductOrder'
    writes = 'PoseidonCompletion.writes'
    source = ('import ShielddSecurity.'+order+'\n'
              'import ShielddSecurity.ScalarProductWriteLowerBound\n'
              'set_option maxHeartbeats 200000\n'
              'namespace ShielddSecurity.'+name+'\n')
    source += f'''private theorem prefix000_lower : ∀ column ∈ {writes} {order}.prefix000, 50200 ≤ column := by
  simp [{order}.prefix000, PoseidonCompletion.writes]
'''
    for index, lower, upper in bounds:
        following = f'{int(index)+1:03d}'
        source += f'''private theorem prefix{following}_lower : ∀ column ∈ {writes} {order}.prefix{following}, 50200 ≤ column := by
  apply ScalarProductWriteLowerBound.append_writes 50200 {order}.prefix{index} {order}.chunk{index} prefix{index}_lower
  intro column member
  have lower := ScalarProductWriteLowerBound.bounded_writes {lower} {upper} {order}.chunk{index} {order}.checked_bound{index} column member
  exact Nat.le_trans (by decide : 50200 ≤ {lower}) lower
'''
    source += '''theorem outside (column : Nat) (below : column < 50200) :
    column ∉ PoseidonCompletion.writes RuntimeTransferIvkReductionProductOrder.allStages := by
  intro written
  have lower := prefix034_lower column written
  omega
set_option pp.all true in
#check @outside
#print axioms outside
end ShielddSecurity.RuntimeIvkReductionLowWrites
'''
    return name, source
