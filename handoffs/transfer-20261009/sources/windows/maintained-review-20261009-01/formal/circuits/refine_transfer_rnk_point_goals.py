"""Normalize concrete column maps before checking field equalities."""


def generate(name, source):
    if name != 'RuntimeRnkNativeSource':
        return source
    for coordinate, original, target in [('x', 1504, 1520), ('y', 1505, 1521)]:
        projection = f'congrArg (fun point : Group.Point F => point.{coordinate})'
        old = f'    exact {projection} paired'
        new = (f'    have equality := {projection} paired\n'
               f'    change sigma {original} = target {target}\n'
               '    exact equality')
        assert source.count(old) == 1
        source = source.replace(old, new)
        old = f'    exact {projection} (sourceFacts.2.2.trans targetPoint.symm)'
        new = (f'    have equality := {projection} (sourceFacts.2.2.trans targetPoint.symm)\n'
               '    exact equality')
        assert source.count(old) == 1
        source = source.replace(old, new)
    return source
