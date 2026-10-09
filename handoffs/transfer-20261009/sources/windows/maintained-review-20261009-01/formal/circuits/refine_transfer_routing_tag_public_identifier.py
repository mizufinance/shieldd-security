"""Escape the captured public-bit identifier for Lean's public keyword."""
import re


def refine(text):
    assert text.count('def public : Linear :=') == 1
    assert '«public»' not in text
    result = re.sub(r'\bpublic\b', '«public»', text)
    assert result.count('def «public» : Linear :=') == 1
    assert re.findall(r'^#check @(.+)$', result, re.M) == re.findall(r'^#check @(.+)$', text, re.M)
    return result
