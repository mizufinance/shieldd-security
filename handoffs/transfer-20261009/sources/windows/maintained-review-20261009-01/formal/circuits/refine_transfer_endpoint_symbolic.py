"""Expose only the completion layers needed by symbolic frame lemmas."""
import re


def generate(source):
    start = source.index('  intro column member\n', source.index('theorem ivk_targets'))
    end = source.index('\nvariable (arithmetic', start)
    source = source[:start] + '''  intro column member
  have choices : column = 1512 ∨ column = 1513 := by
    simpa only [targetColumns,List.mem_cons,List.not_mem_nil,or_false] using member
  have inverseOutside : column ∉ RuntimeTransferIvkInverseOwnedCompletion.ownedWrites := by
    rcases choices with rfl | rfl <;> decide
  have seedOutside : column ∉ [1994,1995] := by
    rcases choices with rfl | rfl <;> decide
  have qOutside : column < 1996 ∨ 1996+4 ≤ column := by
    rcases choices with rfl | rfl <;> decide
  have rOutside : column < 2000 ∨ 2000+252 ≤ column := by
    rcases choices with rfl | rfl <;> decide
  have low : column < 50200 := by
    rcases choices with rfl | rfl <;> decide
  have hashOutside : column ∉ RuntimeTransferIvkHashOwnedCompletion.ownedWrites := by
    rcases choices with rfl | rfl <;> decide
  have viewOutside : column ∉ ShielddViewingKeySeed.columns := by
    rcases choices with rfl | rfl <;> decide
  unfold RuntimeTransferIvkNativeInverseOwned.completeAssignment RuntimeTransferIvkInversePrefixJoin.completed
  rw [RuntimeTransferIvkInverseOwnedCompletion.preserves _ column inverseOutside]
  unfold RuntimeTransferIvkHashReductionJoin.completed RuntimeTransferIvkReductionProductOrder.construct
  rw [ScalarReductionFrame.column _ codec _ 1994 1995 1996 2000
    RuntimeTransferIvkReductionProductOrder.allStages column seedOutside qOutside rOutside
    (RuntimeIvkReductionLowWrites.outside column low)]
  rw [RuntimeTransferIvkHashOwnedCompletion.preserves _ column hashOutside,
    ShielddViewingKeySeed.seed_preserves fq backend nk x y base column viewOutside]''' + source[end:]
    for name, output, target in [('xValue', 3007, 1512), ('yValue', 3008, 1513)]:
        old = f'  · simp [Square,eval,{name}]'
        new = (f'  · change Square (-built {target} + built {output}) 0\n'
               f'    rw [{name}]\n'
               '    simp only [neg_add_cancel,Square,zero_mul]')
        assert source.count(old) == 1
        source = source.replace(old, new)
    assert len(re.findall(r'^#check @', source, re.M)) == 8
    return source
