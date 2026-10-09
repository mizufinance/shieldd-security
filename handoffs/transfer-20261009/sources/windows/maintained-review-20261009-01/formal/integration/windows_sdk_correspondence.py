"""Root-only single Linux-row replay against all eight actual Windows spools.

This is serialized backend correspondence, not Windows platform assurance,
native point semantics, reachability, a circuit proof, or certification.
"""
from contextlib import ExitStack
from pathlib import Path
import hashlib
import json
import struct
import sys

from circuits import transfer_relation

PIN = '16e7b009b763be55ca21f423f4f97e8c132b40b6adbcd06f6a3be17f2d0ef236'
ORIGINAL_RAW = 'fa0de5dba3cc2b75ea56e333d2c60f8b373f0c59f6f9b4aed04fd2f59b7f2c9f'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(65536), b''):
            h.update(block)
    return h.hexdigest()


def bounded_json(path, maximum=4194304):
    with path.open('rb') as stream:
        data = stream.read(maximum + 1)
    require(len(data) <= maximum, 'metadata exceeds finite bound')
    return json.loads(data)


def completed(path):
    result = bounded_json(path / 'result.json', 32768)
    require((path / 'complete.txt').is_file() and result['reason'] == 'completed' and
            result['launched'] and result['assignedBeforeResume'] and result['cleanupComplete'] and
            result['activeAfter'] == 0 and result['exitCode'] == 0, 'actual owned Windows job did not complete')


def compare_term_sequence(stream, expected):
    encoded = stream.read(8)
    require(len(encoded) == 8 and struct.unpack('>Q', encoded)[0] == len(expected), 'actual ordered term count differs')
    for column, coefficient in expected:
        encoded = stream.read(36)
        require(len(encoded) == 36 and encoded[:4] == struct.pack('>I', column) and
                encoded[4:] == bytes.fromhex(coefficient), 'actual ordered column/coefficient differs')


class BoundedLines:
    def __init__(self, stream):
        self.stream = stream

    def readline(self):
        line = self.stream.readline(4194305)
        require(len(line) <= 4194304, 'Linux row exceeds finite bound')
        return line

    def read(self, count):
        return self.stream.read(count)


def verify(spec):
    require(spec['schema'] == 'shieldd-windows-sdk-correspondence-root-v1', 'exact correspondence spec required')
    destination = Path(spec['destination'])
    require(not destination.exists(), 'fresh correspondence receipt required')
    inputs = {Path(path): digest for path, digest in spec['inputs'].items()}
    # Full relation bytes are streamed below once; identity verified there.
    original = Path(spec['original_linux_relation'])
    require(inputs.get(original) == ORIGINAL_RAW, 'exact accepted Linux relation identity required')
    for path, digest in inputs.items():
        if path != original:
            require(sha(path) == digest, 'actual input drift: ' + str(path))
    names = ['ordinary1','ordinary2','epk-first','epk-repeat','variable-first','variable-repeat','blinding-first','blinding-repeat']
    require(set(spec['spools']) == set(names), 'two ordinary plus all three first/repeat captures required')
    required = {original}
    for name in names:
        capture = spec['spools'][name]
        required.update(Path(capture[key]) for key in ['rows','shape'])
        required.update(Path(capture['job']) / key for key in ['spec.json','result.json','complete.txt'])
        if name not in ['ordinary1','ordinary2']:
            required.add(Path(capture['pending']))
    for field in ['unit_jobs','qualifiers']:
        for job in spec[field].values():
            required.update(Path(job) / key for key in ['spec.json','result.json','complete.txt','stdout.txt'])
    require(required <= set(inputs), 'every actual source/test/capture/qualifier input must be pinned')
    executed = set()
    for name in names:
        completed(Path(spec['spools'][name]['job']))
        executed.add(bounded_json(Path(spec['spools'][name]['job']) / 'spec.json', 32768)['executable_sha256'])
    require(len(executed) == 1, 'all captures must execute one actual private binary')
    for name, count in [('epk',7),('variable',3),('blinding',4)]:
        unit = Path(spec['unit_jobs'][name]); completed(unit)
        output = (unit / 'stdout.txt').read_text(errors='strict')
        require('test result: ok. ' + str(count) + ' passed; 0 failed;' in output, 'exact actual native test count required')
    for name, count in [('epk',48),('variable',5),('blinding',8)]:
        qualifier = Path(spec['qualifiers'][name]); completed(qualifier)
        parent = bounded_json(qualifier / 'stdout.txt')
        require(parent['relation_digest'] == PIN and parent['domain_size'] == 262144 and parent['full_rows'] == 200770 and
                parent['constant_copy'] == 200692 and parent['ordinary_full_ordered_rows_equal'] is True and
                parent['repeated_observations_equal'] is True and len(parent['pages']) == count, 'actual closed page qualifier/production identity required')
        for side in ['first','repeat']:
            capture = spec['spools'][name + '-' + side]
            pending = bounded_json(Path(capture['pending']))
            require(pending['ordinary_full_ordered_rows_equal'] is False and pending['repeated_observations_equal'] is False and
                    len(pending['pages']) == count and pending['constant_copy'] == 200692, 'raw pending pages must retain FALSE flags')
    with ExitStack() as stack:
        streams = []
        for name in names:
            capture = spec['spools'][name]
            shape = bounded_json(Path(capture['shape']), 32768)
            require(shape['schema'] == 'shieldd-transfer-ordered-spool-v1' and shape['relation_digest'] == PIN and
                    shape['full_rows'] == 200770 and shape['domain_size'] == 262144 and shape['public_inputs'] == 1 and
                    shape['blocks'] == [1] and shape['source_public'] == [[1,22734]] and shape['source_blocks'] == [[[1,6]]], 'actual production spool layout differs')
            streams.append(stack.enter_context(Path(capture['rows']).open('rb')))
        def observe(row):
            for stream in streams:
                compare_term_sequence(stream, row['a']); compare_term_sequence(stream, row['b'])
        result = transfer_relation.inspect(BoundedLines(stack.enter_context(original.open('rb'))), PIN, observe)
        require(result['raw_sha256'] == ORIGINAL_RAW and result['stored_rows'] == 200770, 'accepted Linux original bytes differ')
        require(all(stream.read(1) == b'' for stream in streams), 'trailing Windows spool bytes')
    for path, digest in inputs.items():
        if path != original:
            require(sha(path) == digest, 'actual input changed during comparison')
    destination.mkdir()
    (destination / 'receipt.json').write_text(json.dumps({'status':'full ordered serialized backend correspondence', 'linux':result,
        'windows_spools':names,'pages':{'epk':48,'variable':5,'blinding':8},'certification':False,
        'semantic_scope':'Only actual source/native test/typed-page qualifier and all ordered rows compared; native model/point and platform state assurance remain separate.'},indent=2,sort_keys=True)+'\n')
    (destination / 'complete.txt').write_text('Eight actual Windows spools equal the full accepted Linux relation; no certification.\n')


if __name__ == '__main__':
    require(len(sys.argv) == 2, 'one root correspondence activation spec required')
    verify(bounded_json(Path(sys.argv[1]),262144))
