"""Reduce point projections without unfolding the constructor assignment."""


def generate(name, source):
    if name != 'RuntimeRnkNativeSource':
        return source
    assert source.count('    exact equality') == 4
    return source.replace('    exact equality', '    dsimp only at equality\n    exact equality')
