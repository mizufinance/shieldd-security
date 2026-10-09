"""Use explicit list membership and Nat domains for the six-scope join."""
from . import generate_transfer_epk_all_scopes_join as previous


def generate(pairs):
    name,text=previous.generate(pairs)
    for i in range(6):
        old='Or.inl rfl'
        new='List.mem_cons.mpr (Or.inl rfl)'
        for _ in range(i):
            old=f'Or.inr ({old})'
            new=f'List.mem_cons.mpr (Or.inr ({new}))'
        old=f'by simp only [blocks,List.mem_cons]; exact {old}'
        assert text.count(old)==1
        text=text.replace(old,f'by exact {new}')
    assert text.count('values.map (fun n =>')==2
    text=text.replace('values.map (fun n =>','values.map (fun n : Nat =>')
    return name,text
