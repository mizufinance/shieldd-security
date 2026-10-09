"""Declare field equality decisions for the selector theorem statement."""


def generate(source):
    old = 'theorem flag_sound (rho : Nat → F)'
    assert source.count(old) == 1
    return source.replace(old, 'theorem flag_sound [DecidableEq F] (rho : Nat → F)')
