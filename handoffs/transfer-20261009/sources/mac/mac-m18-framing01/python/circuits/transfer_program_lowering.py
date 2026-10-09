"""Select complete compiler certificate data from a bounded source-program stream.

The exact pinned compiler is replayed for DATA SELECTION, never as a proof.
SQLite keeps the complete DAG and sparse expressions off the Python heap. Every
selected row must subsequently match the independent ordinary row stream; Lean
must check the selected node/assertion certificates and owned algorithm meaning.
No witness values, assertion truth or satisfying assignment are imported here.
"""
import json
import sqlite3
from copy import deepcopy
from pathlib import Path

from .hash_rows import canonical as _canonical
from .transfer_source_program import FIELD_MODULUS, ProgramError, inspect_stream
from . import transfer_relation


MAX_EXPRESSION_BYTES = 8 * 1024 * 1024
MAX_DATABASE_BYTES = 8 * 1024 * 1024 * 1024
MAX_LINEAR_TERMS = 32768
MAX_ROW_BYTES = 16 * 1024 * 1024


def canonical(terms):
    terms = tuple(terms)
    if len(terms) > 2 * MAX_LINEAR_TERMS:
        raise ProgramError('finite sparse operand bound exceeded')
    result = _canonical(terms)
    if len(result) > MAX_LINEAR_TERMS:
        raise ProgramError('finite sparse result bound exceeded')
    return result


def scaled(terms, coefficient):
    return canonical((column, value * coefficient) for column, value in terms)


def _encoded(value):
    raw = json.dumps(value, separators=(',', ':')).encode()
    if len(raw) > MAX_EXPRESSION_BYTES:
        raise ProgramError('finite sparse expression bound exceeded')
    return raw


def select_stream(stream, database_path, consume=None):
    """Fresh bounded disk selection, with exact source and original row identities.

    The callback receives header, all final node expressions/certificates, all
    column sources, all assertion certificates, and every original outlined row.
    Failure leaves diagnostic data; the caller must discard any partial callback
    output. Only a successful returned report indicates completed selection.
    """
    path = Path(database_path)
    if path.exists():
        raise ProgramError('fresh compiler selection database required')
    db = sqlite3.connect(path)
    try:
        db.execute('PRAGMA cache_size=-16384')
        db.execute('PRAGMA temp_store=FILE')
        db.execute('PRAGMA journal_mode=DELETE')
        db.executescript('''
          CREATE TABLE constants(id INTEGER PRIMARY KEY, value TEXT NOT NULL);
          CREATE TABLE nodes(id INTEGER PRIMARY KEY, op TEXT, lk INT, li INT,
            rk INT, ri INT, assertion_uses INT DEFAULT 0, other_uses INT DEFAULT 0,
            kind TEXT, terms BLOB, certificate BLOB);
          CREATE TABLE assertions(id INTEGER PRIMARY KEY, lk INT, li INT,
            rk INT, ri INT, certificate BLOB);
          CREATE TABLE rows(id INTEGER PRIMARY KEY, a BLOB, b BLOB, origin BLOB);
          CREATE TABLE columns(id INTEGER PRIMARY KEY, source BLOB);
          CREATE TABLE metadata(key TEXT PRIMARY KEY, value BLOB);
        ''')
        header = None

        def disk_bound():
            size = db.execute('PRAGMA page_count').fetchone()[0] * db.execute(
                'PRAGMA page_size').fetchone()[0]
            if size > MAX_DATABASE_BYTES:
                raise ProgramError('finite selection database bound exceeded')

        def bump(ref, field):
            if ref[0] == 2:
                db.execute(f'UPDATE nodes SET {field}={field}+1 WHERE id=?', (ref[1],))

        def ingest(item):
            nonlocal header
            if 'schema' in item:
                header = item
                if header['source_blocks'][0][0][0] == 0:
                    raise ProgramError('committed constant is not an accepted input layout')
            elif 'constant' in item:
                db.execute('INSERT INTO constants VALUES (?,?)',
                           (item['constant'], item['value']))
            elif 'node' in item:
                db.execute('INSERT INTO nodes(id,op,lk,li,rk,ri) VALUES (?,?,?,?,?,?)',
                    (item['node'], item['operation'], *item['left'], *item['right']))
                bump(item['left'], 'other_uses')
                bump(item['right'], 'other_uses')
            else:
                db.execute('INSERT INTO assertions(id,lk,li,rk,ri) VALUES (?,?,?,?,?)',
                    (item['assertion'], *item['left'], *item['right']))
                bump(item['left'], 'assertion_uses')
                bump(item['right'], 'assertion_uses')
            ordinal = item.get('node', item.get('assertion', item.get('constant', 0)))
            if ordinal % 1024 == 0:
                disk_bound()

        identity = inspect_stream(stream, ingest)
        for ref in header['source_public'] + header['source_blocks'][0]:
            bump(ref, 'other_uses')
        next_column = 3 + header['witnesses']
        row_count = 0

        def allocate(source):
            nonlocal next_column
            column = next_column
            next_column += 1
            if next_column > 2**22:
                raise ProgramError('finite compiler column bound exceeded')
            db.execute('INSERT INTO columns VALUES (?,?)', (column, _encoded(source)))
            return column

        def emit(a, b, origin):
            nonlocal row_count
            db.execute('INSERT INTO rows VALUES (?,?,?,?)',
                       (row_count, _encoded(a), _encoded(b), _encoded(origin)))
            row_count += 1
            if row_count > 2**23:
                raise ProgramError('finite compiler row bound exceeded')
            if row_count % 1024 == 0:
                disk_bound()

        def coordinate(column):
            return ((column, 1),)

        def expression(ref):
            kind, ordinal = ref
            if kind == 0:
                value = int(db.execute('SELECT value FROM constants WHERE id=?',
                                       (ordinal,)).fetchone()[0], 16)
                return 'linear', canonical(((0, value),))
            if kind == 1:
                return 'linear', coordinate(3 + ordinal)
            record = db.execute('SELECT kind,terms FROM nodes WHERE id=?',
                                (ordinal,)).fetchone()
            if record is None or record[0] is None:
                raise ProgramError('missing earlier selected expression')
            return record[0], tuple(map(tuple, json.loads(record[1])))

        def linear(ref):
            kind, terms = expression(ref)
            if kind != 'linear':
                raise ProgramError('deferred square consumed as a linear placeholder')
            return terms

        def constant(terms):
            if all(column == 0 for column, _ in terms):
                return sum(value for _, value in terms) % FIELD_MODULUS
            return None

        for ordinal in range(header['nodes']):
            operation, lk, li, rk, ri, assertions, others = db.execute(
                'SELECT op,lk,li,rk,ri,assertion_uses,other_uses FROM nodes WHERE id=?',
                (ordinal,)).fetchone()
            left_ref, right_ref = [lk, li], [rk, ri]
            left, right = linear(left_ref), linear(right_ref)
            cert = dict(node=ordinal, left=left_ref, right=right_ref, rows=[])
            kind = 'linear'
            if operation == 'add':
                output = canonical(left + right)
                cert['constructor'] = 'add'
            elif constant(right) is not None:
                output = scaled(left, constant(right))
                cert.update(constructor='foldedRight', coefficient=constant(right))
            elif constant(left) is not None:
                output = scaled(right, constant(left))
                cert.update(constructor='foldedLeft', coefficient=constant(left))
            elif left == right and assertions == 1 and others == 0:
                kind, output = 'square', left
                cert['constructor'] = 'deferred'
            else:
                output_column = allocate(dict(kind='source', reference=[2, ordinal]))
                output = coordinate(output_column)
                cert['rows'].append(row_count)
                if left == right:
                    cert['constructor'] = 'square'
                    emit(left, output, dict(kind='node', id=ordinal, role='square'))
                else:
                    auxiliary = allocate(dict(kind='differenceSquare', left=left_ref, right=right_ref))
                    cert.update(constructor='product', auxiliary=coordinate(auxiliary))
                    emit(canonical(left + scaled(right, -1)), coordinate(auxiliary),
                         dict(kind='node', id=ordinal, role='minus'))
                    cert['rows'].append(row_count)
                    emit(canonical(left + right), canonical(coordinate(auxiliary) + scaled(output, 4)),
                         dict(kind='node', id=ordinal, role='plus'))
            db.execute('UPDATE nodes SET kind=?,terms=?,certificate=? WHERE id=?',
                       (kind, _encoded(output), _encoded(cert), ordinal))

        for ordinal in range(header['assertions']):
            lk, li, rk, ri = db.execute('SELECT lk,li,rk,ri FROM assertions WHERE id=?',
                                      (ordinal,)).fetchone()
            left_ref, right_ref = [lk, li], [rk, ri]
            left_kind, left = expression(left_ref)
            right_kind, right = expression(right_ref)
            indices = []
            if left_kind == 'square' or right_kind == 'square':
                base, other_ref, other_kind, other = (
                    (left, right_ref, right_kind, right) if left_kind == 'square'
                    else (right, left_ref, left_kind, left))
                if other_kind == 'square':
                    output = coordinate(allocate(dict(kind='source', reference=other_ref)))
                    node_cert = json.loads(db.execute('SELECT certificate FROM nodes WHERE id=?',
                                                     (other_ref[1],)).fetchone()[0])
                    node_cert.update(constructor='square', rows=[row_count])
                    emit(other, output, dict(kind='node', id=other_ref[1],
                         role='assertionMaterializedSquare', materializing_assertion=ordinal))
                    db.execute('UPDATE nodes SET kind=?,terms=?,certificate=? WHERE id=?',
                               ('linear', _encoded(output), _encoded(node_cert), other_ref[1]))
                    other = output
                indices.append(row_count)
                emit(base, other, dict(kind='assertion', id=ordinal, role='fusedSquare'))
                constructor = 'squareLinear' if left_kind == 'square' else 'linearSquare'
            else:
                indices.append(row_count)
                emit(canonical(left + scaled(right, -1)), (),
                     dict(kind='assertion', id=ordinal, role='linear'))
                constructor = 'linear'
            db.execute('UPDATE assertions SET certificate=? WHERE id=?',
                (_encoded(dict(assertion=ordinal, left=left_ref, right=right_ref,
                               constructor=constructor, rows=indices)), ordinal))

        for column, ref, role in [(1, header['source_public'][0], 'public'),
                                  (2, header['source_blocks'][0][0], 'committed')]:
            emit(canonical(coordinate(column) + scaled(linear(ref), -1)), (),
                 dict(kind='input', role=role, column=column, reference=ref))
        copy = allocate(dict(kind='one'))
        # This row is added AFTER outlining all preceding rows. Its column 0
        # remains the actual fixed-one column, exactly as in outline_constant.
        emit(canonical(coordinate(0) + scaled(coordinate(copy), -1)), (),
             dict(kind='constantCopy', column=copy))
        domain = 1 << (max(next_column, row_count, 1) - 1).bit_length()
        disk_bound()
        db.commit()
        if consume is not None:
            def deliver(item):
                consume(deepcopy(item))

            deliver(dict(kind='header', source_identity=identity, domain_size=domain,
                         stored_rows=row_count, constant_copy=copy, allocated_columns=next_column))
            for ordinal, kind, terms, certificate in db.execute(
                    'SELECT id,kind,terms,certificate FROM nodes ORDER BY id'):
                deliver(dict(kind='node', id=ordinal, expression_kind=kind,
                             terms=json.loads(terms), certificate=json.loads(certificate)))
            for ordinal, certificate in db.execute('SELECT id,certificate FROM assertions ORDER BY id'):
                deliver(dict(kind='assertion', id=ordinal, certificate=json.loads(certificate)))
            for column in range(next_column):
                if column == 0:
                    source = dict(kind='one')
                elif column <= 2:
                    source = dict(kind='source', reference=(header['source_public'][0]
                        if column == 1 else header['source_blocks'][0][0]))
                elif column < 3 + header['witnesses']:
                    source = dict(kind='source', reference=[1, column - 3])
                else:
                    source = json.loads(db.execute('SELECT source FROM columns WHERE id=?',
                                                  (column,)).fetchone()[0])
                deliver(dict(kind='column', column=column, source=source))
            for ordinal, a, b, origin in db.execute('SELECT id,a,b,origin FROM rows ORDER BY id'):
                def outlined(raw):
                    terms = tuple(map(tuple, json.loads(raw)))
                    return canonical((copy if column == 0 and ordinal != row_count - 1 else column,
                                      coefficient) for column, coefficient in terms)
                deliver(dict(kind='row', row=ordinal, a=outlined(a), b=outlined(b),
                             origin=json.loads(origin)))
        report = dict(source_identity=identity, selected_nodes=header['nodes'],
                    selected_assertions=header['assertions'], stored_rows=row_count,
                    domain_size=domain, constant_copy=copy, allocated_columns=next_column,
                    padding_column_source='zero', padding_rows='implicit-all-zero',
                    data_selection='PASS', ordinary_full_row_comparison=False,
                    kernel_run=False, owned_assertion_meaning='UNPROVED', proof_credit=0)
        db.execute('INSERT INTO metadata VALUES (?,?)', ('complete', _encoded(report)))
        db.commit()
        return report
    finally:
        db.close()


def compare_stream(stream, database_path, expected_relation=None):
    """Compare every ordered coefficient/body and all source roles to selection.

    BLAKE3 identifies the ordinary stream as an additional identity check. Row
    bodies are compared independently; the digest is never used instead of them.
    This remains source data correspondence, with no kernel or assertion credit.
    """
    path = Path(database_path)
    if not path.is_file():
        raise ProgramError('completed selection database required')
    db = sqlite3.connect(path.resolve().as_uri() + '?mode=ro', uri=True)
    try:
        db.execute('PRAGMA cache_size=-16384')
        entry = db.execute('SELECT value FROM metadata WHERE key=?', ('complete',)).fetchone()
        if entry is None:
            raise ProgramError('incomplete selection database')
        selected = json.loads(entry[0])
        expected_count, copy = selected['stored_rows'], selected['constant_copy']
        compared = 0

        class BoundedStream:
            def readline(self):
                raw = stream.readline(MAX_ROW_BYTES + 1)
                if len(raw) > MAX_ROW_BYTES:
                    raise ProgramError('bounded ordinary row record required')
                return raw

            def read(self, count):
                return stream.read(count)

        def compare(row):
            nonlocal compared
            entry = db.execute('SELECT a,b FROM rows WHERE id=?', (row['row'],)).fetchone()
            if entry is None:
                raise ProgramError('ordinary stream has an unselected row')
            for side, raw in zip(('a', 'b'), entry):
                terms = tuple(map(tuple, json.loads(raw)))
                expected = canonical((copy if column == 0 and row['row'] != expected_count - 1 else column,
                                      coefficient) for column, coefficient in terms)
                actual = tuple((column, int(value, 16)) for column, value in row[side])
                if actual != expected:
                    raise ProgramError(f'ordinary compiler row {row["row"]} side {side} changed')
            compared += 1

        ordinary = transfer_relation.inspect(BoundedStream(), expected_relation, compare)
        source = selected['source_identity']
        if (compared != expected_count or ordinary['stored_rows'] != expected_count
                or ordinary['domain_size'] != selected['domain_size']
                or ordinary['source_public'] != source['source_public']
                or ordinary['source_blocks'] != source['source_blocks']):
            raise ProgramError('complete compiler row count/domain/source layout changed')
        return dict(selection=selected, ordinary_identity=ordinary,
                    ordered_row_body_comparisons=compared, full_row_data_comparison='PASS',
                    kernel_run=False, owned_assertion_meaning='UNPROVED', proof_credit=0)
    finally:
        db.close()
