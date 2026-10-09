"""Evaluate the two endpoint linear forms before rewriting coordinates."""


def generate(source):
    for name, output, target in [('xValue', 3007, 1512), ('yValue', 3008, 1513)]:
        old = f'  · change Square (-built {target} + built {output}) 0\n'
        new = ('  · simp only [eval,Int.cast_neg,Int.cast_one,neg_one_mul,one_mul,add_zero]\n'
               f'    change Square (-built {target} + built {output}) 0\n')
        assert source.count(old) == 1
        source = source.replace(old, new)
    return source
