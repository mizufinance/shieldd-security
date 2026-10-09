"""Import the field modulus explicitly in bounded page composition proofs."""
from . import generate_transfer_receiver_lifecycle_gate_page_completion as original


def generate(page, sources):
    name, text = original.generate(page, sources)
    marker = "import ShielddSecurity.CompilerSequenceCompletion\n"
    assert text.count(marker) == 1
    text = text.replace(marker, "import ShielddSecurity.Scalar\n" + marker)
    marker = "set_option maxHeartbeats 200000\n"
    assert text.count(marker) == 1
    return name, text.replace(marker, marker + "set_option maxRecDepth 4096\n")
