"""Generate narrow canonical-coordinate pages from retained address rows."""
from . import generate_transfer_routing_canonical_pages as pages
from . import refine_transfer_routing_canonical_join as joins
from .transfer_encryption_address_rows import SCHEMA


def generate(extraction):
    assert extraction["schema"] == SCHEMA
    items = extraction["plan"]["decompositions"]
    assert len(items) == 8 and len({item["role"] for item in items}) == 8
    result = {}
    for item in items:
        assert len(item["plan"]["columns"]) == len(item["plan"]["steps"]) == 255
        prefix = "RuntimeEncryptionAddress" + item["role"] + "Canonical"
        derivative = dict(
            schema="shieldd-transfer-routing-row-derivative-v1",
            selected_rows=extraction["selected_rows"],
            plan=dict(permutation=item["plan"], constant_link=extraction["plan"]["constant_link"]),
        )
        for name, text in {**pages.generate(derivative), **joins.generate(derivative)}.items():
            fresh = name.replace("RuntimeRoutingCanonical", prefix)
            assert fresh not in result
            # Keep the already audited symbolic theory namespaces unchanged.
            result[fresh] = text.replace("RuntimeRoutingCanonicalPage", prefix + "Page").replace(
                "RuntimeRoutingCanonicalJoin", prefix + "Join"
            )
    assert len(result) == 136
    return result
