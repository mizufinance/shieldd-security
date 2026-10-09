"""Use Lean's step-one range interval lemma for captured routing prefixes."""


def generate(name, source):
    if name == 'RuntimeRoutingPrefixTheory':
        return source
    assert name in ['RuntimeRoutingPrecision0Prefix', 'RuntimeRoutingPrecision1Prefix']
    assert source.count("List.mem_range'") == 2
    return source.replace("List.mem_range'", "List.mem_range'_1")
