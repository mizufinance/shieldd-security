"""Permit empty lines between Lean's scoped printing option and its command.

This adapter changes only the audit parser's view. Source hashes, compiled
objects, dependency snapshots, printed statements, and axiom checks retain
their original bytes and requirements. A nonempty intervening command remains
visible, so an absent or different scoped printing option still fails.
"""
from collections.abc import Callable


def exported_signatures_with_blank_lines(
    source: str, strict_parser: Callable[[str], list[str]]
) -> list[str]:
    lines = source.splitlines()
    # Only genuinely empty ASCII whitespace lines are omitted. Comments and
    # other Lean commands must still be checked by the strict named parser.
    compact = "\n".join(line for line in lines if line.strip(" \t") != "")
    return strict_parser(compact)
