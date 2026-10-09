"""Pure source recipe for a future diagnostic compiler, never the active stage."""
from pathlib import Path


def instrument_compiler(data,resource=None,tests=None):
    if not isinstance(data,bytes):raise ValueError('fresh compiler source bytes required')
    if b'pub fn compile_inspected_pages' in data:raise ValueError('paged inspection already activated')
    resource=resource if resource is not None else (Path(__file__).parent/'observers/compile_inspected_pages.rs').read_bytes()
    tests=tests if tests is not None else (Path(__file__).parent/'observers/compile_inspected_pages_tests.rs').read_bytes()
    if not isinstance(resource,bytes) or not isinstance(tests,bytes):raise ValueError('paged resource/test bytes required')
    newline=b'\r\n' if b'\r\n' in data else b'\n'
    if newline==b'\r\n' and b'\n' in data.replace(b'\r\n',b''):raise ValueError('compiler mixed line endings')
    normalized=data.replace(b'\r\n',b'\n')
    anchor=b'    /// Compile a generic arithmetic circuit into a canonical square relation.\n'
    if normalized.count(anchor)!=1 or normalized.count(b'    pub fn compile_inspected(')!=1:
        raise ValueError('owned inspected compiler anchor drift')
    body=b'\n'.join(b'    '+line if line else line for line in resource.replace(b'\r\n',b'\n').split(b'\n'))
    normalized=normalized.replace(anchor,body+b'\n'+anchor)
    normalized+=b'\n'+tests.replace(b'\r\n',b'\n')
    return normalized.replace(b'\n',newline)


def replace_owned_pages(data, prior_resource, prior_tests, resource=None, tests=None):
    """Replace an exactly identified owned adapter; preserve the ordinary compiler."""
    if not all(isinstance(value, bytes) for value in (data, prior_resource, prior_tests)):
        raise ValueError('exact prior owned compiler resource and tests required')
    newline = b'\r\n' if b'\r\n' in data else b'\n'
    if newline == b'\r\n' and b'\n' in data.replace(b'\r\n', b''):
        raise ValueError('compiler mixed line endings')
    normalized = data.replace(b'\r\n', b'\n')
    body = b'\n'.join(b'    ' + line if line else line
                      for line in prior_resource.replace(b'\r\n', b'\n').split(b'\n')) + b'\n'
    suffix = b'\n' + prior_tests.replace(b'\r\n', b'\n')
    if normalized.count(body) != 1 or not normalized.endswith(suffix):
        raise ValueError('prior owned page adapter or test bytes drifted')
    base = normalized.removesuffix(suffix).replace(body, b'', 1)
    return instrument_compiler(base.replace(b'\n', newline), resource, tests)
