from pathlib import Path
from datetime import datetime, timezone
import ast
import hashlib
import json
import re
import sys

repo = Path('C:/src/shieldd-formal')
diag = repo/'.work/diagnostics/transfer-implementation-20261002'
pub = Path('C:/src/shieldd-transfer-windows-publication-20261009/handoffs/transfer-20261009')
sys.path.insert(0, str(repo))
sys.path.insert(0, str(diag/'python-deps'))
from circuits import transfer_relation as relation

sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
load = lambda path: json.loads(path.read_text(encoding='utf-8-sig'))
out = diag/'mac-M17-indexed-rows-3237'
assert not out.exists(), 'fresh diagnostic row certificate required'
closure = pub/'sources/windows/mac-M17-range-inclusion-imports-3219'
manifest = load(closure/'manifest.json')
source = closure/'ShielddSecurity/RuntimeBalanceBlindingCanonical.lean'
bridge = closure/'ShielddSecurity/TransferCommittedBlindingRangeBridge.lean'
assert sha(source) == manifest['sources']['RuntimeBalanceBlindingCanonical']['sha256']
assert sha(bridge) == manifest['sources']['TransferCommittedBlindingRangeBridge']['sha256']
source_bytes, bridge_bytes = source.read_bytes(), bridge.read_bytes()
text = source_bytes.decode().replace('\r\n', '\n')
assert re.findall(r'^def copyColumn : Nat := (\d+)$', text, re.M) == ['200692']
assert re.findall(r'^def p : Nat := (\d+)$', text, re.M) == [str(relation.MODULUS)]
names = [f'c{i}' for i in range(16)] + ['tail']
assert re.findall(r'^def originalBlocks : List \(List Row\) := (.*)$', text, re.M) == [
    '[' + ', '.join(name+'Raw' for name in names) + ']']
assert re.findall(r'^def originalRows : List Row := (.*)$', text, re.M) == ['originalBlocks.flatten']
assert re.findall(r'^def rows : List Row := (.*)$', text, re.M) == ['unoutlineRows copyColumn originalRows']
assert ('[⟨[(2, 1), (9, (Scalar.modulus - 1 : Nat))], []⟩]' in
        bridge_bytes.decode().replace('\r\n', '\n'))
entries, blocks = [], []
for name in names:
    indices_literals = re.findall(r'^def '+name+r'OriginalIndices : List Nat := (.*)$', text, re.M)
    rows_literals = re.findall(r'^def '+name+r'Raw : List Row := (.*)$', text, re.M)
    assert len(indices_literals) == len(rows_literals) == 1, name
    # Only exact literal lists/pairs/integers are accepted, never Lean execution
    # or evaluation of an arbitrary Python expression.
    indices = ast.literal_eval(indices_literals[0])
    rows = ast.literal_eval(rows_literals[0].replace('⟨', '(').replace('⟩', ')'))
    assert isinstance(indices, list) and isinstance(rows, list) and len(indices) == len(rows)
    block = []
    for position, (index, sides) in enumerate(zip(indices, rows)):
        assert type(index) is int and 0 <= index < 200770
        assert isinstance(sides, tuple) and len(sides) == 2
        for terms in sides:
            assert isinstance(terms, list)
            previous = -1
            for term in terms:
                assert isinstance(term, tuple) and len(term) == 2
                column, value = term
                assert type(column) is type(value) is int
                assert previous < column < 262144 and 0 < value < relation.MODULUS
                previous = column
        entry = dict(block=name, block_position=position, capture_index=index,
                     a=sides[0], b=sides[1])
        entries.append(entry)
        block.append(index)
    blocks.append(dict(block=name, rows=len(rows), indices=block))
input_entry = dict(block='committedInput', block_position=0, capture_index=200768,
                   a=[(2, 1), (9, relation.MODULUS-1)], b=[])
entries.insert(0, input_entry)
expected = {entry['capture_index']: entry for entry in entries}
assert len(expected) == len(entries) == 758
assert len(blocks) == 17 and sum(item['rows'] for item in blocks) == 757
assert blocks[-1]['indices'] == [200769, 200510, 200512]
matched = set()
raw = diag/'cargo-capture-02/relation.jsonl'

class BoundedRows:
    def __init__(self, handle): self.handle = handle
    def readline(self):
        line = self.handle.readline(4194305)
        assert len(line) <= 4194304, 'bounded full-capture record required'
        return line
    def read(self, count): return self.handle.read(count)

def observe(row):
    if row['row'] in expected:
        entry = expected[row['row']]
        assert row['row'] not in matched
        for side in ['a', 'b']:
            actual = [(column, int(value, 16)) for column, value in row[side]]
            assert actual == entry[side], (entry['block'], entry['block_position'], row['row'], side)
        matched.add(row['row'])

with raw.open('rb') as handle:
    identity = relation.inspect(BoundedRows(handle),
        '16e7b009b763be55ca21f423f4f97e8c132b40b6adbcd06f6a3be17f2d0ef236', observe)
assert identity['raw_sha256'] == 'fa0de5dba3cc2b75ea56e333d2c60f8b373f0c59f6f9b4aed04fd2f59b7f2c9f'
assert identity['stored_rows'] == 200770 and identity['domain_size'] == 262144
assert identity['source_public'] == [[1, 22734]] and identity['source_blocks'] == [[[1, 6]]]
assert matched == set(expected)
assert source.read_bytes() == source_bytes and bridge.read_bytes() == bridge_bytes
out.mkdir()
certificate = out/'indexed-row-bodies.jsonl'
with certificate.open('wb') as handle:
    handle.write((json.dumps(dict(schema='shieldd-transfer-M17-indexed-row-bodies-v1',
        local_rows_order='committedInput ++ originalBlocks.flatten', rows=len(entries),
        runtime_sha='844389ee069e1fb2e576708842d0b389b4d9a44a',
        raw_identity=identity, canonical_source_sha256=sha(source), bridge_source_sha256=sha(bridge),
        comparison='exact original index and ordered canonical integer row bodies',
        kernel_full_row_inclusion=False), separators=(',', ':'))+'\n').encode())
    for entry in entries:
        handle.write((json.dumps(entry, separators=(',', ':'))+'\n').encode())
    handle.write((json.dumps(dict(end=True, rows=len(entries)), separators=(',', ':'))+'\n').encode())
receipt = dict(observed_utc=datetime.now(timezone.utc).isoformat(),
    runtime_sha='844389ee069e1fb2e576708842d0b389b4d9a44a',
    complete_stream_identity=identity, complete_rows_read=200770,
    exact_index_body_comparisons=758, canonical_original_rows=757, input_rows=1,
    blocks=blocks, special_rows=dict(outlined_copy=200769, committed_input=200768,
                                  bit_reconstruction=200510, canonical_final=200512),
    canonical_source_sha256=sha(source), bridge_source_sha256=sha(bridge),
    closure_manifest_sha256=sha(closure/'manifest.json'),
    certificate_sha256=sha(certificate), certificate_bytes=certificate.stat().st_size,
    generator_sha256=sha(Path(__file__)),
    raw_whole_capture_published=False, generated_Lean_or_source_changed=False,
    actual_source_data_correspondence='PASS', kernel_full_row_inclusion=False,
    semantic_control_credit=0, proof_credit=0, full_transfer='OPEN',
    scope='Every owned committed-blinding row matches its exact original full-capture index/body. '
          'This is bounded source data correspondence, not a kernel theorem of fullRows membership. '
          'M17 must keep complete-at-index identity explicit until actual complete relation instance '
          'is replayed/qualified; M18 fresh ordinary capture can check these exact 758 bodies again.')
(out/'receipt.json').write_bytes((json.dumps(receipt, indent=2)+'\n').encode())
print(json.dumps(dict(packet=str(out), rows=758, blocks=17,
    certificate_sha256=sha(certificate), receipt_sha256=sha(out/'receipt.json'), proof_credit=0)))
