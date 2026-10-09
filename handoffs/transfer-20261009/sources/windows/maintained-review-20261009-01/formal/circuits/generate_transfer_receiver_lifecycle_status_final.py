"""Bound the concrete 131-column layout reduction in the final status join."""
from . import generate_transfer_receiver_lifecycle_status_join as original


def generate_join():
    name, text = original.generate_join()
    marker = "set_option maxHeartbeats 250000\n"
    assert text.count(marker) == 1
    return name, text.replace(marker, marker + "set_option maxRecDepth 4096\n")
