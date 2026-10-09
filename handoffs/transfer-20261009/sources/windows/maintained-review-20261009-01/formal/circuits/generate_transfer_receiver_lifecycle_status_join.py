"""Maintain the final status proof separately from retained status pages."""
from . import generate_transfer_receiver_lifecycle_status as status
from . import transfer_relation as relation


def generate_join():
    name, text = status.generate_join()
    before = "      exact List.mem_range'.mpr ⟨lower,by omega⟩"
    after = "      exact List.mem_range'.mpr ⟨i-67,by omega,by simp only [Nat.one_mul]; omega⟩"
    if text.count(before) != 1:
        raise relation.RelationError('exact captured status range-membership proof required')
    text = text.replace(before, after)
    before = "    simp only [layout,List.getElem_range']"
    after = "    simp only [layout,List.getElem_range',Nat.one_mul]"
    if text.count(before) != 1:
        raise relation.RelationError('exact captured status column-layout proof required')
    return name, text.replace(before, after)
