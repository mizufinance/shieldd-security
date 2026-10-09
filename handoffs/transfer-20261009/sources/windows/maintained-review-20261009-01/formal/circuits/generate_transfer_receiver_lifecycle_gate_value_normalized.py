"""Normalize the unit status subtraction without changing captured operands."""
from . import generate_transfer_receiver_lifecycle_gate_value as original


def generate(gate_source,index,column,regulated):
    name,text=original.generate(gate_source,index,column,regulated)
    old=',eval,one,enabled,mul_comm] using product'
    new=',eval,one,enabled,mul_comm,sub_eq_add_neg,add_comm] using product'
    assert text.count(old)==1
    return name,text.replace(old,new)
