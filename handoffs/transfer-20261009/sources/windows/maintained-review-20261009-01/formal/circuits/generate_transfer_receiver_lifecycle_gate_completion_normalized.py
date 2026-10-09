"""Normalize the status subtraction in the captured local construction proof."""
from . import generate_transfer_receiver_lifecycle_gate_completion as original


def generate(gate_source,index):
    name,text=original.generate(gate_source,index)
    old=',eval,one,flagValue,bitValue,mul_comm] using'
    new=',eval,one,flagValue,bitValue,mul_comm,sub_eq_add_neg,add_comm] using'
    assert text.count(old)==1
    return name,text.replace(old,new)
