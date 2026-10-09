"""Repair the checked RNK adapter's source membership and elaboration.

The physical source/target rows and constructors remain unchanged. Window
ownership is finite checked inclusion, because physical row ordering differs
from the proved modules' concatenation order.
"""
import re


def generate(name, source):
    source = re.sub(r'\b(RuntimeRnkNativeSource|C)\.prefix\b', r'\1.nativePrefix', source)
    if name == 'RuntimeRnkNativeSource' or re.fullmatch(r'RuntimeRnkSparseBlock\d{3}', name):
        pattern = r'theorem source_rows_owned : sourceRows = (RuntimeOwnershipWindow\d{3}\.rawRows) := by decide'
        def inclusion(match):
            target = match.group(1)
            return (f'theorem source_rows_owned : ∀ row ∈ sourceRows, row ∈ {target} := by\n'
                    f'  have checked : sourceRows.all (fun row => decide (row ∈ {target})) = true := by decide\n'
                    '  intro row member\n'
                    '  exact of_decide_eq_true (List.all_eq_true.mp checked row member)')
        source = re.sub(pattern, inclusion, source)
    if name.startswith('RuntimeRnkNativeChunk'):
        # Bit blocks retain their exact equality to the Boolean range list.
        def membership(match):
            block = match.group(1)
            if re.search(r'\b' + re.escape(block) + r'\.source_rows_owned', source):
                return f'  have member := {block}.source_rows_owned row member'
            raise AssertionError('missing ownership claim')
        # The plan inserts a bit block after every sixteen window blocks.
        source = re.sub(r'  rw \[(RuntimeRnkSparseBlock(\d{3}))\.source_rows_owned\] at member',
                        lambda m: m.group(0) if int(m.group(2)) % 17 == 16 or int(m.group(2)) == 133
                        else membership(m), source)
    if name != 'RuntimeRnkNativeSource':
        return source
    source = re.sub(r'\bprefix\b', 'nativePrefix', source)
    old = '  rw [source_rows_owned] at member'
    assert source.count(old) == 1
    source = source.replace(old, '  have member := source_rows_owned row member')
    old = ('  simp only [RuntimeOwnershipConstructorChunk000.originalBlocks,List.mem_cons,List.not_mem_nil,or_false]\n'
           '  exact Or.inl rfl')
    assert source.count(old) == 1
    source = source.replace(old, '  exact List.mem_cons.mpr (Or.inl rfl)')
    old = '  exact ⟨(kept 0 (by decide)).trans one,by rw [kept 200692 (by decide),kept 0 (by decide),linked]⟩'
    assert source.count(old) == 1
    source = source.replace(old, '  exact ⟨(kept 0 (by decide)).trans one, (kept 200692 (by decide)).trans (linked.trans (kept 0 (by decide)).symm)⟩')
    old = ('    rw [RuntimeOwnershipNativeConstructor.ivk_constants fq backend codec nk x y base 200692 (by simp),\n'
           '      RuntimeOwnershipNativeConstructor.ivk_constants fq backend codec nk x y base 0 (by simp),linked]')
    new = ('    exact (RuntimeOwnershipNativeConstructor.ivk_constants fq backend codec nk x y base 200692 (by simp)).trans\n'
           '      (linked.trans (RuntimeOwnershipNativeConstructor.ivk_constants fq backend codec nk x y base 0 (by simp)).symm)')
    assert source.count(old) == 1
    source = source.replace(old, new)
    old = '  rw [value]\n  cases RuntimeOwnershipNativeConstructor.nativeBits'
    assert source.count(old) == 1
    source = source.replace(old, '  unfold sourceAssignment\n  rw [value]\n  cases RuntimeOwnershipNativeConstructor.nativeBits')
    start = source.index('  let seeded :=', source.index('private theorem ivk_input_preserved'))
    end = source.index('\ninclude arithmetic', start)
    source = source[:start] + '''  unfold nativePrefix RuntimeTransferIvkNativeInverseOwned.completeAssignment RuntimeTransferIvkInversePrefixJoin.completed
  rw [RuntimeTransferIvkInverseOwnedCompletion.preserves _ column facts.2.2.2.2.1]
  unfold RuntimeTransferIvkHashReductionJoin.completed RuntimeTransferIvkReductionProductOrder.construct
  rw [ScalarReductionFrame.column _ codec _ 1994 1995 1996 2000
    RuntimeTransferIvkReductionProductOrder.allStages column facts.1 facts.2.1 facts.2.2.1 facts.2.2.2.1]
  rw [RuntimeTransferIvkHashOwnedCompletion.preserves _ column facts.2.2.2.2.2.1,
    ShielddViewingKeySeed.seed_preserves fq backend nk x y _ column facts.2.2.2.2.2.2]''' + source[end:]
    return source
