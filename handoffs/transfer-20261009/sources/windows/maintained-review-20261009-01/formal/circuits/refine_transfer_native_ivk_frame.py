"""Replace wide IVK product-write decisions with the checked allocation bound.

Only proof bodies and a helper import change. The fully checked source packets
remain the input; captured rows, constructors and public theorem types stay fixed.
"""
import re


def endpoint(source):
    for column in (1512, 1513):
        old = ('RuntimeTransferIvkReductionProductOrder.allStages '+str(column)+
               ' (by decide) (by decide) (by decide) (by decide)')
        new = ('RuntimeTransferIvkReductionProductOrder.allStages '+str(column)+
               ' (by decide) (by decide) (by decide) '
               '(RuntimeIvkReductionLowWrites.outside '+str(column)+' (by decide))')
        assert source.count(old) == 1
        source = source.replace(old, new)
    return 'import ShielddSecurity.RuntimeIvkReductionLowWrites\n'+source


def rnk_native(source):
    start = source.index('  have checks : [1520,1521].all ')
    end = source.index('\n  let seeded :=', start)
    old = source[start:end]
    assert 'PoseidonCompletion.writes RuntimeTransferIvkReductionProductOrder.allStages' in old
    replacement = '''  have choices : column = 1520 ∨ column = 1521 := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
  have low : column < 50200 := by
    rcases choices with rfl | rfl <;> decide
  have facts : column ∉ [1994,1995] ∧
      (column < 1996 ∨ 1996+4 ≤ column) ∧
      (column < 2000 ∨ 2000+252 ≤ column) ∧
      column ∉ PoseidonCompletion.writes RuntimeTransferIvkReductionProductOrder.allStages ∧
      column ∉ RuntimeTransferIvkInverseOwnedCompletion.ownedWrites ∧
      column ∉ RuntimeTransferIvkHashOwnedCompletion.ownedWrites ∧
      column ∉ ShielddViewingKeySeed.columns := by
    refine ⟨?_, ?_, ?_, RuntimeIvkReductionLowWrites.outside column low, ?_, ?_, ?_⟩
    all_goals rcases choices with rfl | rfl <;> decide'''
    refined = 'import ShielddSecurity.RuntimeIvkReductionLowWrites\n'+source[:start]+replacement+source[end:]
    assert re.findall(r'^#check @(.+)$', refined, re.M) == re.findall(r'^#check @(.+)$', source, re.M)
    return refined
