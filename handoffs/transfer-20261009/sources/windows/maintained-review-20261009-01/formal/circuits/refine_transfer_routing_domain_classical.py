"""Supply classical decidability inside the existing domain proof only."""


def generate(name, source):
    assert name in ['RuntimeRoutingPrecision0Domain', 'RuntimeRoutingPrecision1Domain']
    old = '    ∃ precision : Nat, precision < 33 ∧ eval rho input = (precision : F) := by\n'
    assert source.count(old) == 1
    return source.replace(old, old + '  classical\n')
