"""Audit the exact legacy scalar helper's repeated axiom commands.

Its original body printed twelve axiom reports; its appended full-signature
audit repeats those reports. Both reports remain mandatory. This narrow adapter
does not change source, object, dependency, or compiler identity checks.
"""
from collections.abc import Callable
import hashlib
import re

from circuits.lean_named_signature_spacing import exported_signatures_with_blank_lines


LEGACY_MODULE = "ScalarChunkComposition"
LEGACY_SHA256 = "8ef0c3a9160ffb9b11ed7c7077326e2d4fcc97eb16613d59dc11b7a5f77e525a"
NAMESPACE = "ShielddSecurity.ScalarChunkComposition"


def named_signatures(
    source: str, strict_parser: Callable[[str], list[str]], module: str, source_sha: str
) -> list[str]:
    if module != LEGACY_MODULE or source_sha != LEGACY_SHA256:
        return exported_signatures_with_blank_lines(source, strict_parser)
    # The only normalization permitted for this identity is removal of the
    # twelve original axiom-print commands from the parser view. They are
    # independently matched, counted, and checked in the actual compiler output.
    lines = source.splitlines()
    first = next(i for i, line in enumerate(lines) if line.startswith("#check @"))
    prefix = lines[:first]
    original = []
    retained = []
    for line in prefix:
        match = re.fullmatch(r"#print axioms ([\w.]+)\s*", line)
        if match:
            assert "." not in match[1]
            original.append(NAMESPACE + "." + match[1])
        else:
            retained.append(line)
    names = exported_signatures_with_blank_lines(
        "\n".join(retained + lines[first:]), strict_parser
    )
    assert len(names) == 12 and names == original
    assert len(re.findall(r"^#print axioms ", source, re.M)) == 24
    return names


def axiom_report_count(module: str, source_sha: str) -> int:
    return 2 if (module, source_sha) == (LEGACY_MODULE, LEGACY_SHA256) else 1


def check_printed_axioms(output: str, name: str, count: int) -> None:
    reports = re.findall(
        "'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", output
    )
    empty = re.findall("'" + re.escape(name) + "' does not depend on any axioms", output)
    assert len(reports) + len(empty) == count
    permitted = {"propext", "Classical.choice", "Quot.sound"}
    assert all(set(re.findall(r"[\w.]+", report)) <= permitted for report in reports)
