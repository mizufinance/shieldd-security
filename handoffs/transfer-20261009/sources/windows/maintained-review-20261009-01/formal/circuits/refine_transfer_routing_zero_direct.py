"""Use the already proved compiler row lemmas directly on the seven rows."""
import re


def generate(source):
    old = 'import ShielddSecurity.ScalarComparisonBounds\n'
    assert source.count(old) == 1
    source = source.replace(old, '')
    for right, output in [('inverse', 'inverseOutput'), ('flag', 'zeroOutput')]:
        pattern = (r'ScalarRows\.checked_product_sound rho one four expectedRows rows\n'
                   r'    denominator ' + right + ' ' + output + r' \(\.product (\[[^\n]+\])\) \(by decide\)')
        source, count = re.subn(pattern, lambda m: 'Compiler.checked_product_sound rho expectedRows\n'
                               '    denominator ' + right + ' ' + output + ' ' + m.group(1) +
                               ' four rows (by decide) (by decide)', source)
        assert count == 1
    old = ('ScalarComparisonBounds.checked_equality rho expectedRows rows\n'
           '    inverseOutput ([(0,1)] ++ scaleLinear (-1) flag) (by decide)')
    new = ('Compiler.checked_assertion_sound rho expectedRows\n'
           '    inverseOutput ([(0,1)] ++ scaleLinear (-1) flag) rows (by decide)')
    assert source.count(old) == 1
    source = source.replace(old, new)
    old = 'ScalarComparisonBounds.checked_equality rho expectedRows rows zeroOutput [] (by decide)'
    assert source.count(old) == 1
    source = source.replace(old, 'Compiler.checked_assertion_sound rho expectedRows zeroOutput [] rows (by decide)')
    return source
