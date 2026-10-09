"""Prove captured gate membership explicitly before constructing its pivots."""
from . import generate_transfer_receiver_lifecycle_gate_completion_normalized as original


def generate(gate_source, index):
    name, text = original.generate(gate_source, index)
    old = "flag (by decide) legal)"
    assert text.count(old) == 1
    return name, text.replace(old, "flag (by simp [ReceiverLifecycle.GateIndex]) legal)")
