"""Independent readonly SQL, signed recipes and exact extraction replay."""
from pathlib import Path
import hashlib, json, sqlite3, subprocess

J = Path(__file__).parent
W = J.parent
P = 52435875175126190479447740508185965837690552500527637822603658699938581184513
def sha(b): return hashlib.sha256(b).hexdigest()
def canonical(terms):
    sums = {}
    for column, coefficient in terms:
        sums[column] = (sums.get(column, 0) + coefficient) % P
    return [[column, value] for column, value in sorted(sums.items()) if value]
def outline(terms): return sorted([[200692 if column == 0 else column, value] for column, value in terms])
tasks = [('high-zero126', 'mac-registry-high-zero126-data01', 'f26157e0698fb78114c722852ef839772a913e9ab3c667f22935572cdf660ac3', 125375, 125889),
         ('low-limb129', 'mac-registry-low-limb129-data01', '6bb30f2c82b92484125c9548b74957ad2e01ba50bc82aca848d109dbc88a1af1', 125890, 126791)]
for label, folder, digest, start, end in tasks:
    D = J / (label + '-data-review01')
    D.mkdir()
    S = W / folder
    raw = (S / 'selected-data01.json').read_bytes()
    assert sha(raw) == digest
    q = json.loads(raw)
    R = D / 'extraction-replay01'
    R.mkdir()
    original = (S / 'extract.py').read_bytes()
    (R / 'extract-original.py').write_bytes(original)
    text = original.decode()
    old = 'S=Path(__file__).resolve().parent;W=S.parent;'
    assert text.count(old) == 1
    changed = text.replace(old, 'S=Path(__file__).resolve().parent;W=Path(' + repr(str(W)) + ');')
    (R / 'extract-replay.py').write_text(changed)
    run = subprocess.run(['python3', '-I', '-B', '-S', str(R / 'extract-replay.py')], capture_output=True, timeout=60)
    assert run.returncode == 0, run.stderr.decode()
    assert (R / 'selected-data01.json').read_bytes() == raw
    db = Path(q['database']['path'])
    before = (db.stat().st_size, db.stat().st_mtime_ns)
    assert before == (q['database']['bytes'], q['database']['mtime_ns'])
    c = sqlite3.connect(db.as_uri() + '?mode=ro&immutable=1', uri=True)
    c.execute('PRAGMA cache_size=-8192')
    c.execute('PRAGMA query_only=ON')
    nodes = {r[0]: dict(id=r[0], op=r[1], lk=r[2], li=r[3], rk=r[4], ri=r[5], kind=r[6], terms=json.loads(r[7]), certificate=json.loads(r[8]))
             for r in c.execute('SELECT id,op,lk,li,rk,ri,kind,terms,certificate FROM nodes WHERE id BETWEEN ? AND ?', (start, end))}
    assert len(nodes) == q['source_nodes'] == end - start + 1
    assert q['source_span'] == [start, end]
    assert sha(json.dumps(nodes, sort_keys=True, separators=(',', ':')).encode()) == q['source_node_lc_sha256']
    for key, value in q['constants'].items():
        assert int(c.execute('SELECT value FROM constants WHERE id=?', (int(key),)).fetchone()[0], 16) == value
    expected = []
    if label == 'high-zero126':
        delta = canonical([[599+i, 2**i] for i in range(127)] + [[344+i, -2**i] for i in range(127)])
        assert q['delta'] == delta == nodes[125884]['terms']
        assert q['zero'] == 1110 and q['inverse'] == 1111 and q['write_window'] == [1110, 1112]
        for offset, (flag, product, auxiliary, sign) in enumerate([(1111, 33770, 33771, -1), (1111, 33770, 33771, 1), (1110, 33772, 33773, -1), (1110, 33772, 33773, 1)]):
            a = canonical(delta + [[flag, sign]])
            b = [[auxiliary, 1]] if sign == -1 else canonical([[auxiliary, 1], [product, 4]])
            rawrow = c.execute('SELECT a,b,origin FROM rows WHERE id=?', (11032+offset,)).fetchone()
            aa, bb, origin = map(json.loads, rawrow)
            assert aa == a and bb == b
            e = q['arithmetic_rows'][offset]
            assert e == dict(index=11032+offset, a=a, b=b, outlined_a=outline(a), outlined_b=outline(b), origin=origin)
            assert origin == dict(kind='node', id=125886 if offset < 2 else 125889, role='minus' if sign == -1 else 'plus')
        assert len(q['arithmetic_rows']) == 4
        assert nodes[125886]['certificate']['rows'] == [11032, 11033]
        assert nodes[125889]['certificate']['rows'] == [11034, 11035]
        expected = [([[1110, 1]], [[1110, 1]]), (canonical([[33770, 1], [1110, 1], [0, -1]]), []), ([[33772, P-1]], [])]
        first = 179023
        boolean_count = 1
    else:
        assert nodes[126145]['terms'] == [[471+i, 2**i] for i in range(128)]
        assert nodes[126401]['terms'] == [[216+i, 2**i] for i in range(128)]
        assert q['borrow'] == 1112 and q['difference'] == 1113 and q['bits'] == [1114, 1242]
        assert q['hints_write_window'] == [1112, 1242] and q['arithmetic_rows_allocated'] == 0
        assert q['original_input_low_asset'] == [471, 599] and q['original_input_low_value'] == [216, 344]
        expected = [([[1112 if i == 0 else 1113+i, 1]], [[1112 if i == 0 else 1113+i, 1]]) for i in range(129)]
        expected += [(canonical([[1113, -1]] + [[1114+i, 2**i] for i in range(128)]), []),
                     (canonical([[216+i, 2**i] for i in range(128)] + [[471+i, -2**i] for i in range(128)] + [[1112, 2**128], [1113, -1]]), [])]
        first = 179026
        boolean_count = 129
    assert len(q['rows']) == len(expected)
    for offset, (a, b) in enumerate(expected):
        index = first + offset
        assertion = index - 177954
        aa, bb, origin = map(json.loads, c.execute('SELECT a,b,origin FROM rows WHERE id=?', (index,)).fetchone())
        e = q['rows'][offset]
        assert e['index'] == index and e['assertion'] == assertion
        assert aa == a == e['a'] and bb == b == e['b']
        assert e['outlined_a'] == outline(a) and e['outlined_b'] == outline(b)
        assert origin == e['origin'] == dict(kind='assertion', id=assertion, role='fusedSquare' if offset < boolean_count else 'linear')
        ar = c.execute('SELECT lk,li,rk,ri,certificate FROM assertions WHERE id=?', (assertion,)).fetchone()
        cert = json.loads(ar[4])
        assert cert == e['certificate'] and cert['assertion'] == assertion
        assert cert['left'] == list(ar[:2]) and cert['right'] == list(ar[2:4]) and cert['rows'] == [index]
    for key in ['binary_qualification', 'range_source', 'registry_source']:
        pin = q[key]
        data = Path(pin['path']).read_bytes()
        assert len(data) == pin['bytes'] and sha(data) == pin['sha256']
    c.close()
    assert before == (db.stat().st_size, db.stat().st_mtime_ns)
    report = dict(status='PASSED', kind='DATA only; exact original extraction replay plus independent readonly SQL and signed row recipes',
                  selected_data_sha256=digest, raw_nodes=len(nodes), constants=len(q['constants']),
                  actual_assertion_rows=len(expected), actual_arithmetic_rows=4 if label == 'high-zero126' else 0,
                  positions=[first, first+len(expected)-1], every_row_and_original_certificate_exact=True,
                  independent_signed_recipe_match=True, database_metadata_preserved=True,
                  original_extract_sha256=sha(original), replay_delta='Only output directory placement; all original source/data/DB pins remain identical',
                  full_transfer='OPEN', native_correspondence='OPEN')
    with (D / 'data-review01.json').open('x') as f:
        json.dump(report, f, indent=2)
        f.write('\n')
    print(json.dumps(report))
