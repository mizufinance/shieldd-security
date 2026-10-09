"""Pure source append for the remaining live Transfer caller obligations.

No runtime mutation, compilation, observer acceptance or proof is performed.
The caller must first validate the exact pin and complete parent inventory.
Actual first/repeat observations and both complete ordinary spools remain required.
"""
from pathlib import Path
import json

from .asset_map_observer import _source

PREFIX = 'crates/crypto/circuits/'
MODULE = PREFIX + 'src/transfer/remaining_inspection.rs'
CATALOGUE = PREFIX + 'src/catalogue.rs'
EXPORTER = PREFIX + 'examples/transfer-ownership-inspection.rs'
FRAGMENTS = Path(__file__).resolve().parent / 'observers'
DISPATCH = '    let args: Vec<_> = std::env::args().skip(1).collect();'
MODE = ('\n    if args.len()==3 && args[0]=="remaining-pages-spool" {\n'
        '        return capture_transfer_remaining_pages(&args[1],&args[2]);\n    }')
DECLARATION = '\n#[cfg(feature = "formal-observer")]\npub mod remaining_inspection;\n'
QUALIFIER_SCHEMA = '        Some("shieldd-transfer-note-hash-pages-v1") |'
QUALIFIER_BRANCH = '            if pending["schema"] == "shieldd-transfer-t4-recovery-pages-v1" {'
QUALIFIER_ADD = ('            if pending["schema"] == "shieldd-transfer-remaining-source-pages-v1" {\n'
                 '                qualify_remaining_pages(first,repeated,&pending)?;\n            }\n')


def hooks():
    return json.loads((FRAGMENTS / 'transfer_remaining_hooks.json').read_bytes())


def instrument(data, operations):
    """Unique anchors, preserved newline convention, reversible text changes."""
    text, newline = _source(data)
    if 'remaining_inspection' in text:
        raise ValueError('remaining observer already present')
    before = text
    if not isinstance(operations, list) or not operations:
        raise ValueError('remaining hooks required')
    for operation in operations:
        if (not isinstance(operation, dict) or set(operation) !=
                {'anchor', 'replacement', 'kind', 'expected_count'} or
                operation['kind'] != 'replace' or
                type(operation['expected_count']) is not int or
                operation['expected_count'] != 1 or
                not isinstance(operation['anchor'], str) or not operation['anchor'] or
                not isinstance(operation['replacement'], str) or
                operation['replacement'] == operation['anchor']):
            raise ValueError('invalid remaining source hook')
        anchor = operation['anchor']
        if text.count(anchor) != 1:
            raise ValueError('remaining unique source anchor drift')
        text = text.replace(anchor, operation['replacement'])
    reversed_text = text
    for operation in reversed(operations):
        replacement = operation['replacement']
        if reversed_text.count(replacement) != 1:
            raise ValueError('remaining hook reversal ambiguous')
        reversed_text = reversed_text.replace(replacement, operation['anchor'])
    if reversed_text != before:
        raise ValueError('remaining parent text not preserved')
    return text.replace('\n', newline).encode()


def compose(files):
    """Append to the complete existing source overlay; never replace old modes."""
    if not isinstance(files, dict) or MODULE in files:
        raise ValueError('fresh remaining child source required')
    operations = hooks()
    required = set(operations) | {CATALOGUE, EXPORTER}
    if any(not isinstance(files.get(path), bytes) for path in required):
        raise ValueError('complete retained remaining caller sources required')
    result = dict(files)
    for path, changes in operations.items():
        result[path] = instrument(files[path], changes)
    transfer = PREFIX + 'src/transfer.rs'
    text, newline = _source(result[transfer])
    result[transfer] = (text + DECLARATION).replace('\n', newline).encode()
    for path, fragment in [(CATALOGUE, 'transfer_remaining_catalogue.rs'),
                           (EXPORTER, 'transfer_remaining_export.rs')]:
        text, newline = _source(files[path])
        if 'RemainingPage' in text or 'capture_transfer_remaining_pages' in text:
            raise ValueError('remaining append already present')
        if path == EXPORTER:
            if text.count(DISPATCH) != 1:
                raise ValueError('remaining exporter main dispatch changed')
            text = text.replace(DISPATCH, DISPATCH + MODE)
            if text.count(QUALIFIER_SCHEMA) != 1 or text.count(QUALIFIER_BRANCH) != 1:
                raise ValueError('remaining existing four-spool qualifier changed')
            text = text.replace(QUALIFIER_SCHEMA,
                '        Some("shieldd-transfer-remaining-source-pages-v1") |\n' + QUALIFIER_SCHEMA)
            text = text.replace(QUALIFIER_BRANCH, QUALIFIER_ADD + QUALIFIER_BRANCH)
            qualifier = (FRAGMENTS / 'transfer_remaining_qualification.rs').read_text().replace('\r\n', '\n')
            text += '\n' + qualifier
        addition = (FRAGMENTS / fragment).read_text().replace('\r\n', '\n')
        result[path] = (text + '\n' + addition).replace('\n', newline).encode()
    result[MODULE] = (FRAGMENTS / 'transfer_remaining_roles.rs').read_bytes()
    return result
