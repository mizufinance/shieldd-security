"""Pure exact-pin test overlay for the live Transfer index-mode source boundary.

No runtime stage is edited, no prover is invoked, and these deliberately injected
canonical queue fixtures supply no admitted-Transfer or semantic-negative credit.
"""
import hashlib
from pathlib import Path

HOST = 'crates/core/app/src/app/host.rs'
CONTROL = 'crates/core/app/src/app/fv_transfer_indexing_controls.rs'
HOST_SHA256 = 'fc1c43378105957364e85054f5818eede0702ba9fc5a9d413f53669cb0bfab1d'
ANCHOR = b'#[cfg(test)]\nmod tests {\n    use super::*;\n'
HOOK = (b'    include!(concat!(env!("CARGO_MANIFEST_DIR"), '
        b'"/src/app/fv_transfer_indexing_controls.rs"));\n')
RESOURCE = Path(__file__).resolve().parents[1] / 'state/transfer_indexing_controls.rs'

SERVICE_TESTS = 'crates/bin/shieldd/src/service_contract_tests.rs'
READBACK_CONTROL = 'crates/bin/shieldd/src/fv_transfer_readback_controls.rs'
READBACK_HOOK = (b'\ninclude!(concat!(env!("CARGO_MANIFEST_DIR"), '
                 b'"/src/fv_transfer_readback_controls.rs"));\n')
READBACK_RESOURCE = Path(__file__).resolve().parents[1] / 'state/transfer_readback_controls.rs'
SERVICE_TESTS_SHA256 = '8244de15035011b5bb5dadd3cc567b29e86ee2fe3985a77608869c9d88a55f45'

def compose(overlays, base_host):
    """Append one test include while preserving every inherited overlay byte."""
    if not isinstance(overlays, dict) or not isinstance(base_host, bytes):
        raise ValueError('indexing source overlay requires bytes and an inherited overlay map')
    current = overlays.get(HOST, base_host)
    if not isinstance(current, bytes) or hashlib.sha256(current).hexdigest() != HOST_SHA256:
        raise ValueError('indexing Host source does not match exact accepted pin')
    if current.count(ANCHOR) != 1 or HOOK in current or CONTROL in overlays:
        raise ValueError('indexing control include/resource changed or duplicated')
    result = dict(overlays)
    result[HOST] = current.replace(ANCHOR, ANCHOR + HOOK, 1)
    result[CONTROL] = RESOURCE.read_bytes()
    return result

def compose_readback_controls(overlays, base_service_tests):
    """Append a scoped no-prover query control to the existing owned test module."""
    if not isinstance(overlays, dict) or not isinstance(base_service_tests, bytes):
        raise ValueError('readback source overlay requires bytes and an inherited overlay map')
    current = overlays.get(SERVICE_TESTS, base_service_tests)
    if not isinstance(current, bytes) or hashlib.sha256(current).hexdigest() != SERVICE_TESTS_SHA256:
        raise ValueError('readback service tests do not match exact accepted pin')
    if READBACK_HOOK in current or READBACK_CONTROL in overlays:
        raise ValueError('readback control include/resource changed or duplicated')
    result = dict(overlays)
    result[SERVICE_TESTS] = current + READBACK_HOOK
    result[READBACK_CONTROL] = READBACK_RESOURCE.read_bytes()
    return result
