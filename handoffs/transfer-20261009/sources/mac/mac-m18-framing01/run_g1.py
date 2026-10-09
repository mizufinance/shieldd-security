import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time

STAGE=Path(__file__).resolve().parent
ROOT=STAGE.parents[1]
OUT=ROOT/'outputs/mac-m18-framing01'
OLD=ROOT/'work/parent-full-program'
PUB=ROOT/'work/shared-build-handoff/handoffs/transfer-20261009'
DB=OLD/'capture/lowering-resume01.sqlite'


def digest(path):
    value=hashlib.sha256()
    with Path(path).open('rb') as stream:
        while raw:=stream.read(1024**2):
            value.update(raw)
    return value.hexdigest()


def write(name,value):
    target=OUT/name
    assert not target.exists(),'preserve prior receipt: '+name
    target.write_text(json.dumps(value,indent=2)+'\n')


def worker():
    sys.path.insert(0,str(STAGE/'python'))
    from circuits.transfer_spool import SpoolJSONL, load_shape
    from circuits.transfer_program_lowering import compare_stream
    from circuits.transfer_relation import record, terms, MODULUS
    from circuits.transfer_certificate_export import export_database, verify_export
    inputs=json.loads((OUT/'input-manifest.json').read_text())
    for entry in inputs['sources']:
        assert digest(STAGE/entry['path'])==entry['sha256'],entry['path']
    packet=PUB/'sources/windows/full-program-lowering-3239'
    manifest=json.loads((packet/'manifest.json').read_text())
    assert digest(packet/'manifest.json')=='974bdd9661686e419e0363bf230da87ca83af09b94453d86356711550840709e'
    for name,entry in manifest['sources'].items():
        if name.startswith('formal/'):
            path=STAGE/'python'/name.removeprefix('formal/')
            # The frozen synthetic tests remain in the old stage, byte-exact.
            if name.startswith('formal/tests/'):
                path=OLD/'python'/name.removeprefix('formal/')
            assert digest(path)==entry['sha256'],name
    index_packet=PUB/'sources/windows/mac-M17-indexed-rows-3237'
    assert digest(index_packet/'manifest.json')=='01f31024b9fa1e181c865e40accca07e326e6ceac12075366c6019fe33e1e8a5'
    certificate=index_packet/'indexed-row-bodies.jsonl'
    assert digest(certificate)=='f658f4c86b33ea69072dbc169f8624bc3658909ee7f5c8c57ed5b3375c8f6798'
    with certificate.open('rb') as stream:
        header=record(stream.readline(65537)); expected={}
        assert header['rows']==758 and header['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
        for _ in range(758):
            entry=record(stream.readline(65537)); index=entry['capture_index']
            assert type(index) is int and 0<=index<200770 and index not in expected
            for side in ['a','b']:
                terms([[c,f'{v:064x}'] for c,v in entry[side]],262144)
            expected[index]=entry
        assert record(stream.readline(65537))==dict(end=True,rows=758)
        assert not stream.read(1)
    matched=set()
    def observe(row):
        index=row['row']
        if index in expected:
            assert index not in matched
            for side in ['a','b']:
                actual=[[c,int(v,16)] for c,v in row[side]]
                if actual!=expected[index][side]:
                    raise ValueError(f'M17 exact row {index} side {side} changed')
            matched.add(index)
    with (OLD/'capture/ordinary01.shape.json').open('rb') as stream:
        shape=load_shape(stream)
    assert shape['relation_digest']==header['raw_identity']['relation_digest']
    assert shape['source_public']==[[1,22734]] and shape['source_blocks']==[[[1,6]]]
    assert shape['full_rows']==200770 and shape['domain_size']==262144
    started=time.monotonic()
    with (OLD/'capture/ordinary01.rows').open('rb') as stream:
        adapter=SpoolJSONL(stream,shape,observe)
        comparison=compare_stream(adapter,DB,shape['relation_digest'])
        framing=adapter.receipt()
    assert len(matched)==758
    assert framing['binary_sha256']=='5f28e65e804c05828a6cd66515293e28af77a502e4b066f05d162ae33e4ca0c9'
    comparison_receipt=dict(status='passed',comparison=comparison,adapter=framing,
        m17_index_body_comparisons=len(matched),m17_blocks=17,seconds=time.monotonic()-started,
        runtime_sha=header['runtime_sha'],kernel_run=False,kernel_full_rows_instance=False,
        proof_credit=0,full_transfer='OPEN')
    write('comparison01.json',comparison_receipt)
    print('Full ordered 200770row comparison +758M17 exact body/index replay PASS',flush=True)
    started=time.monotonic()
    target=OUT/'complete-certificates01.jsonl.gz'
    exported=export_database(DB,target)
    write('certificate-export01.json',dict(exported,seconds=time.monotonic()-started))
    print('Complete callback-equivalent certificate export PASS',flush=True)
    started=time.monotonic()
    verified=verify_export(target)
    assert verified['raw_sha256']==exported['raw_sha256']
    write('certificate-verification01.json',dict(verified,seconds=time.monotonic()-started,
        gzip_sha256=digest(target),kernel_run=False,proof_credit=0))
    for entry in inputs['sources']:
        assert digest(STAGE/entry['path'])==entry['sha256'],entry['path']
    write('result01.json',dict(status='passed',gate='G1 complete diagnostic data',
        ordered_row_body_comparisons=200770,m17_index_body_comparisons=758,
        callback_records=exported['callback_records'],certificate_counts=exported['counts'],
        runtime_sha=header['runtime_sha'],lock_qualified_certification=False,
        kernel_run=False,owned_assertion_meaning='UNPROVED',proof_credit=0,full_transfer='OPEN'))
    print('Complete certificate framing/count/hash replay PASS; G1 data only',flush=True)


def guarded():
    sources=[]
    for path in sorted(STAGE.rglob('*.py')):
        sources.append(dict(path=str(path.relative_to(STAGE)),bytes=path.stat().st_size,sha256=digest(path)))
    write('input-manifest.json',dict(sources=sources,selection_database=str(DB),
        original_failed_attempt='outputs/mac-full-source-program/lowering-resume01-run.json',
        tests=16,tests_log_sha256=digest(OUT/'adapter-export-tests01.log'),proof_credit=0))
    receipt=OUT/'guarded-run01.json'; log=OUT/'guarded-run01.log'
    assert not receipt.exists() and not log.exists()
    command=[str(OLD/'venv/bin/python'),str(Path(__file__).resolve()),'--worker']
    result=dict(command=command,status='running',timeout_seconds=900,
        rss_limit_bytes=2*1024**3,min_memory_free_percent=15,min_disk_free_bytes=2*1024**3)
    receipt.write_text(json.dumps(result,indent=2)+'\n')
    started=time.monotonic(); peak=0; min_memory=100; min_disk=shutil.disk_usage(STAGE).free
    with log.open('w') as output:
        child=subprocess.Popen(command,cwd=STAGE,stdout=output,stderr=subprocess.STDOUT,
            env=dict(os.environ,LEAN_NUM_THREADS='1',RAYON_NUM_THREADS='1'),start_new_session=True)
        while child.poll() is None:
            pressure=subprocess.check_output(['memory_pressure'],text=True)
            free=re.search(r'System-wide memory free percentage: (\d+)%',pressure)
            memory=int(free.group(1)) if free else 0
            rss_text=subprocess.run(['ps','-o','rss=','-p',str(child.pid)],capture_output=True,text=True).stdout.strip()
            rss=int(rss_text or 0)*1024; disk=shutil.disk_usage(STAGE).free
            peak=max(peak,rss); min_memory=min(min_memory,memory); min_disk=min(min_disk,disk)
            reason=None
            if time.monotonic()-started>900: reason='time bound'
            elif memory<15: reason='memory pressure'
            elif disk<2*1024**3: reason='free disk'
            elif rss>2*1024**3: reason='RSS bound'
            if reason:
                os.killpg(child.pid,signal.SIGTERM); child.wait()
                result.update(status='interrupted',reason=reason); break
            time.sleep(1)
    result.update(exit=child.returncode,seconds=time.monotonic()-started,peak_rss_bytes=peak,
                  minimum_memory_free_percent=min_memory,minimum_disk_free_bytes=min_disk)
    if result['status']=='running': result['status']='passed' if child.returncode==0 else 'failed'
    receipt.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)
    sys.exit(0 if result['status']=='passed' else 1)


if __name__=='__main__':
    worker() if sys.argv[1:]==['--worker'] else guarded()
