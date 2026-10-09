"""Replay the completed selection callback from read-only SQLite; data only."""
import gzip
import hashlib
import json
from pathlib import Path
import sqlite3

from .transfer_program_lowering import canonical, MAX_DATABASE_BYTES
from .transfer_source_program import ProgramError


def export_database(database, target):
    path, target = Path(database), Path(target)
    if not path.is_file() or path.stat().st_size > MAX_DATABASE_BYTES:
        raise ProgramError('bounded completed database required')
    if target.exists():
        raise ProgramError('fresh complete certificate output required')
    db = sqlite3.connect(path.resolve().as_uri()+'?mode=ro', uri=True)
    db.execute('PRAGMA cache_size=-16384')
    try:
        row = db.execute('SELECT value FROM metadata WHERE key="complete"').fetchone()
        if row is None:
            raise ProgramError('completed selection required')
        selected = json.loads(row[0])
        identity = selected['source_identity']
        counts = identity['counts']
        expected = dict(node=counts['nodes'], assertion=counts['assertions'],
                        column=selected['allocated_columns'], row=selected['stored_rows'])
        for table, total in [('constants',counts['constants']),('nodes',expected['node']),
                            ('assertions',expected['assertion']),('rows',expected['row'])]:
            actual = db.execute(f'SELECT count(*),min(id),max(id) FROM {table}').fetchone()
            if actual != (total, 0 if total else None, total-1 if total else None):
                raise ProgramError('complete ordered selection table required: '+table)
        header = dict(kind='header', source_identity=identity, domain_size=selected['domain_size'],
                      stored_rows=selected['stored_rows'], constant_copy=selected['constant_copy'],
                      allocated_columns=selected['allocated_columns'])
        digest = hashlib.sha256()
        observed = dict(node=0, assertion=0, column=0, row=0)
        raw_bytes = 0
        # Exclusive target means failures retain partial output that lacks a
        # verified complete trailer/receipt; no overwrite of successful exports.
        with target.open('xb') as raw_output:
            with gzip.GzipFile(fileobj=raw_output,mode='wb',mtime=0,compresslevel=1) as output:
                def emit(item):
                    nonlocal raw_bytes
                    data = (json.dumps(item,separators=(',',':'))+'\n').encode()
                    if len(data) > 32*1024**2:
                        raise ProgramError('bounded exported certificate record required')
                    raw_bytes += len(data)
                    if raw_bytes > 8*1024**3 or raw_output.tell() > 4*1024**3:
                        raise ProgramError('finite certificate export bound exceeded')
                    digest.update(data)
                    output.write(data)
                emit(header)
                for ordinal,kind,terms,certificate in db.execute(
                        'SELECT id,kind,terms,certificate FROM nodes ORDER BY id'):
                    cert = json.loads(certificate)
                    if ordinal != observed['node'] or cert['node'] != ordinal:
                        raise ProgramError('ordered node certificate required')
                    emit(dict(kind='node',id=ordinal,expression_kind=kind,
                              terms=json.loads(terms),certificate=cert))
                    observed['node'] += 1
                for ordinal,certificate in db.execute('SELECT id,certificate FROM assertions ORDER BY id'):
                    cert = json.loads(certificate)
                    if ordinal != observed['assertion'] or cert['assertion'] != ordinal:
                        raise ProgramError('ordered assertion certificate required')
                    emit(dict(kind='assertion',id=ordinal,certificate=cert))
                    observed['assertion'] += 1
                for column in range(selected['allocated_columns']):
                    if column == 0:
                        source = dict(kind='one')
                    elif column <= 2:
                        source = dict(kind='source',reference=(identity['source_public'][0]
                            if column == 1 else identity['source_blocks'][0][0]))
                    elif column < 3+counts['witnesses']:
                        source = dict(kind='source',reference=[1,column-3])
                    else:
                        source = json.loads(db.execute('SELECT source FROM columns WHERE id=?',
                                                       (column,)).fetchone()[0])
                    emit(dict(kind='column',column=column,source=source))
                    observed['column'] += 1
                for ordinal,a,b,origin in db.execute('SELECT id,a,b,origin FROM rows ORDER BY id'):
                    if ordinal != observed['row']:
                        raise ProgramError('ordered original row required')
                    def outlined(raw):
                        return canonical((selected['constant_copy'] if col == 0
                            and ordinal != expected['row']-1 else col,value)
                            for col,value in json.loads(raw))
                    emit(dict(kind='row',row=ordinal,a=outlined(a),b=outlined(b),origin=json.loads(origin)))
                    observed['row'] += 1
                if observed != expected:
                    raise ProgramError('complete callback export counts required')
                payload_sha = digest.hexdigest()
                trailer = dict(kind='complete',counts=observed,payload_sha256=payload_sha,
                               callback_records=1+sum(observed.values()),kernel_run=False,proof_credit=0)
                emit(trailer)
        return dict(status='passed',schema='shieldd-transfer-complete-lowering-callback-jsonl-gzip-v1',
                    counts=observed,callback_records=1+sum(observed.values()),
                    payload_sha256=payload_sha,raw_sha256=digest.hexdigest(),raw_bytes=raw_bytes,
                    gzip_bytes=target.stat().st_size,
                    callback_replay_from_completed_database=True,kernel_run=False,proof_credit=0)
    finally:
        db.close()


def verify_export(target):
    """Independent streaming framing/count/hash check, no theorem authority."""
    digest=hashlib.sha256()
    observed=dict(node=0,assertion=0,column=0,row=0)
    seen_header=False
    expected=None
    phase=-1
    with gzip.open(target,'rb') as stream:
        while True:
            raw=stream.readline(32*1024**2+1)
            if not raw or len(raw)>32*1024**2 or not raw.endswith(b'\n'):
                raise ProgramError('complete bounded callback framing required')
            record=json.loads(raw)
            kind=record['kind']
            if kind=='complete':
                if not seen_header or expected!=observed or record['counts']!=observed or record['payload_sha256']!=digest.hexdigest() \
                        or record['callback_records']!=1+sum(observed.values()) or stream.read(1):
                    raise ProgramError('complete callback trailer/count/hash required')
                digest.update(raw)
                return dict(status='passed',counts=observed,raw_sha256=digest.hexdigest())
            if kind=='header':
                if seen_header or any(observed.values()):
                    raise ProgramError('one initial callback header required')
                seen_header=True
                expected=dict(node=record['source_identity']['counts']['nodes'],
                              assertion=record['source_identity']['counts']['assertions'],
                              column=record['allocated_columns'],row=record['stored_rows'])
            else:
                if not seen_header or kind not in observed:
                    raise ProgramError('ordered callback kind required')
                current=['node','assertion','column','row'].index(kind)
                if current<phase:
                    raise ProgramError('ordered callback section required')
                phase=current
                ordinal=record['column' if kind=='column' else 'row' if kind=='row' else 'id']
                if type(ordinal) is not int or ordinal!=observed[kind]:
                    raise ProgramError('complete ordered callback identity required')
                observed[kind]+=1
            digest.update(raw)
