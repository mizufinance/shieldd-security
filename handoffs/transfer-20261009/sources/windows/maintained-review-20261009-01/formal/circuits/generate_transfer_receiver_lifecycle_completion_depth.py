"""Bound concrete allocation-frame reductions in the symbolic whole join."""
from . import generate_transfer_receiver_lifecycle_completion as original


def generate(floors):
    name, text = original.generate(floors)
    marker = "set_option maxHeartbeats 300000\n"
    assert text.count(marker) == 1
    return name, text.replace(marker, marker + "set_option maxRecDepth 4096\n")
