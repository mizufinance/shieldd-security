"""Fresh-stage complete source-program export; never patch an active checkout.

The ordinary compiler is unchanged. Complete constants/nodes/assertions and
input-role layout are streamed beside the ordinary full row spool. Qualification
still requires exact repeated graph and independent whole-row comparisons, then
owned algorithm meaning and kernel lowering/topology/assertion certificates.
"""
from pathlib import Path


def _source(data):
    if not isinstance(data, bytes):
        raise ValueError('fresh source bytes required')
    newline = b'\r\n' if b'\r\n' in data else b'\n'
    if newline == b'\r\n' and b'\n' in data.replace(b'\r\n', b''):
        raise ValueError('mixed source line endings')
    return data.replace(b'\r\n', b'\n'), newline


def instrument_circuit(data, resource=None):
    source, newline = _source(data)
    resource = resource if resource is not None else (
        Path(__file__).parent/'observers/inspect_full_program.rs').read_bytes()
    body, _ = _source(resource)
    if b'inspect_program_counts' in source:
        raise ValueError('complete program inspection already present')
    anchor = b'impl<F> Circuit<F> {\n'
    if source.count(anchor) != 1:
        raise ValueError('exact generic Circuit impl required')
    methods = b'\n'.join(b'    '+line if line else line for line in body.split(b'\n'))
    return source.replace(anchor, anchor+methods+b'\n', 1).replace(b'\n', newline)


def instrument_catalogue(data, resource=None):
    source, newline = _source(data)
    resource = resource if resource is not None else (
        Path(__file__).parent/'observers/catalogue_full_program.rs').read_bytes()
    body, _ = _source(resource)
    if b'fn inspect_transfer_program' in source:
        raise ValueError('complete program catalogue already present')
    # Keep the exact ordinary source entry point and its operations unchanged.
    required = [b'pub fn compile(family: Family) -> Result<Compiled> {',
        b'let (c, selected) = circuit::build(|ctx| w.constrain(ctx, &p, &g, &Scalar::zero()));',
        b'let layout = InputLayout::new(vec![selected[0]], vec![vec![selected[1]]])?;',
        b'let relation = Relation::compile(&c, &layout)?;']
    if any(source.count(value) != 1 for value in required):
        raise ValueError('ordinary catalogue compile source shape changed')
    return (source+b'\n'+body).replace(b'\n', newline)


def instrument_exporter(data, resource=None):
    source, newline = _source(data)
    resource = resource if resource is not None else (
        Path(__file__).parent/'observers/export_full_program.rs').read_bytes()
    body, _ = _source(resource)
    if b'fn capture_full_program' in source or b'"full-program-spool"' in source:
        raise ValueError('complete source program exporter already present')
    anchor = b'    let args: Vec<_> = std::env::args().skip(1).collect();\n'
    if source.count(anchor) != 1:
        raise ValueError('exact existing exporter entry required')
    mode = b'    if args.len() == 2 && args[0] == "full-program-spool" {\n' \
           b'        return capture_full_program(&args[1]);\n    }\n'
    return (source.replace(anchor, anchor+mode, 1)+b'\n'+body).replace(b'\n', newline)
