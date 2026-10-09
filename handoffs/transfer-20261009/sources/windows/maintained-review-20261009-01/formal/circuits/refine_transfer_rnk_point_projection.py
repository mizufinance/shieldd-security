"""Fix the field type before elaborating native point projections."""


def generate(name, source):
    if name != 'RuntimeRnkNativeSource':
        return source
    for coordinate in ['x', 'y']:
        old = 'congrArg Group.Point.' + coordinate
        assert source.count(old) == 2
        source = source.replace(old, f'congrArg (fun point : Group.Point F => point.{coordinate})')
    return source
