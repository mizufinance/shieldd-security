"""Avoid expanding scalar/row definitions when joining six audited EPK scopes."""
from . import generate_transfer_epk_all_scopes as original


def generate(pairs):
    name, text = original.generate(pairs)
    for i in range(6):
        old = f'by simp [blocks]'
        member = 'Or.inl rfl'
        for _ in range(i):
            member = f'Or.inr ({member})'
        text = text.replace(old, f'by simp only [blocks,List.mem_cons]; exact {member}', 1)
    old = '    rcases member with rfl | rfl | rfl | rfl | rfl | rfl\n'
    new = '    rcases member with h | h | h | h | h | h\n'
    assert text.count(old) == 1
    text = text.replace(old,new)
    for i in range(6):
        old = f'    · exact ⟨derived{i}.1,derived{i}.2.1⟩'
        new = f'    · rw [h]; exact ⟨derived{i}.1,derived{i}.2.1⟩'
        assert text.count(old) == 1
        text = text.replace(old,new)
    old = '    rcases inside with rfl | rfl | rfl | rfl | rfl | rfl\n'
    new = '    rcases inside with h | h | h | h | h | h\n'
    assert text.count(old) == 1
    text = text.replace(old,new)
    for i in range(6):
        old = f'    · exact sat6_{i} row contained'
        new = f'    · rw [h] at contained; exact sat6_{i} row contained'
        assert text.count(old) == 1
        text = text.replace(old,new)
    return name,text
