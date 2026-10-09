"""Proof-neutral markers locate a bounded compiler's failing declaration."""
import re


def generate(source):
    pattern = re.compile(r'^(include [^\n]+ in\n)?((?:private )?theorem ([A-Za-z0-9_]+))', re.M)
    def mark(match):
        return '#eval "proof declaration: '+match.group(3)+'"\n'+match.group(0)
    result, count = pattern.subn(mark, source)
    assert count > 0
    return result
