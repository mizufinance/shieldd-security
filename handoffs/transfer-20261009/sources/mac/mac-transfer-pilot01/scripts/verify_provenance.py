"""Rebind the finite pilot to unchanged raw inputs, source bytes and ordered rows."""
import hashlib,json,os,re,shutil,signal,sqlite3,subprocess,sys,time
from pathlib import Path
STAGE=Path(__file__).resolve().parent
ROOT=STAGE.parents[1]
OUT=ROOT/'outputs/mac-transfer-pilot01'
CAPTURE=ROOT/'work/parent-full-program/capture'
PIN='844389ee069e1fb2e576708842d0b389b4d9a44a'
def digest(path):
    result=hashlib.sha256()
    with path.open('rb') as stream:
        while data:=stream.read(1024**2):result.update(data)
    return result.hexdigest()
def identity(path):return dict(bytes=path.stat().st_size,sha256=digest(path))
def worker():
    sys.path.insert(0,str(ROOT/'work/mac-m18-framing01/python'))
    from circuits.transfer_source_program import inspect_stream
    from circuits.transfer_program_lowering import compare_stream
    from circuits.transfer_spool import SpoolJSONL,load_shape
    from circuits.transfer_relation import MODULUS
    pilot=json.loads((OUT/'pilot-data01.json').read_text())
    metadata=json.loads((ROOT/'outputs/mac-m18-framing01/comparison01.json').read_text())
    recipe=json.loads((ROOT/'outputs/mac-full-source-program/preparation.json').read_text())
    pinned=ROOT/'outputs/mac-row-replay/pinned-inputs.json'
    assert digest(pinned)=='3b7a2bf22c8429bab961caa690fcf2fd39adaf84f6b3c2fdf31f539f10f76fde'
    runtime=json.loads(pinned.read_text());assert runtime['runtime']==recipe['runtime_pin']==PIN
    baseline=ROOT/'work/runtime-snapshot';stage=ROOT/'work/parent-full-program/runtime'
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=baseline,text=True).strip()==PIN
    assert not subprocess.check_output(['git','status','--porcelain'],cwd=baseline,text=True).strip()
    overlays={x['path']:x for x in recipe['changes']}
    sources=[]
    for item in runtime['all_tracked_inputs']:
        name=item['path'];assert digest(baseline/name)==item['sha256'],name
        expected=overlays.get(name,{}).get('stage_sha256',item['sha256'])
        assert digest(stage/name)==expected,name
        sources.append(dict(path=name,baseline_sha256=item['sha256'],capture_sha256=expected))
    assert len(sources)==1209
    inputs={name:identity(CAPTURE/name) for name in ['lowering-resume01.sqlite',
        'program01.program.jsonl','ordinary01.rows','ordinary01.shape.json']}
    assert inputs['ordinary01.rows']['sha256']==metadata['adapter']['binary_sha256']
    assert inputs['program01.program.jsonl']['sha256']==pilot['source_identity']['raw_sha256']
    assert inputs['ordinary01.shape.json']['sha256']=='bb5bb1ad221386cf87d1ce75aaff4d7ee3e148803f4abf082f9108dbd73683cb'
    db=sqlite3.connect((CAPTURE/'lowering-resume01.sqlite').resolve().as_uri()+'?mode=ro',uri=True)
    complete=json.loads(db.execute('SELECT value FROM metadata WHERE key="complete"').fetchone()[0])
    assert complete==metadata['comparison']['selection']
    assert complete['source_identity']==pilot['source_identity']
    constants=set();nodes=set();assertions=set()
    def source_record(record):
        if 'schema' in record:assert int(record['field_modulus'])==MODULUS
        if record.get('constant') in range(3):
            i=record['constant'];assert int(record['value'],16)==pilot['constants'][i];constants.add(i)
        if record.get('node') in range(8):
            i=record['node'];expected=pilot['arithmetic_nodes'][i]
            assert record==dict(node=i,operation=expected['op'],left=expected['left'],right=expected['right'])
            nodes.add(i)
        if record.get('assertion')==0:
            assert record==dict(assertion=0,left=pilot['assertion']['left'],right=pilot['assertion']['right'])
            assertions.add(0)
    with (CAPTURE/'program01.program.jsonl').open('rb') as stream:
        source=inspect_stream(stream,source_record)
    assert source==pilot['source_identity'] and constants==set(range(3)) and nodes==set(range(8)) and assertions=={0}
    selected={x['capture_index']:x for x in pilot['rows']};seen=set()
    def captured_row(row):
        index=row['row']
        if index in selected:
            for side in ['a','b']:
                assert [[column,int(value,16)] for column,value in row[side]]==selected[index][side]
            seen.add(index)
    with (CAPTURE/'ordinary01.shape.json').open('rb') as stream:shape=load_shape(stream)
    with (CAPTURE/'ordinary01.rows').open('rb') as stream:
        adapter=SpoolJSONL(stream,shape,captured_row)
        comparison=compare_stream(adapter,CAPTURE/'lowering-resume01.sqlite',shape['relation_digest'])
        framing=adapter.receipt()
    assert seen==set(selected) and comparison['ordered_row_body_comparisons']==200770
    assert {name:identity(CAPTURE/name) for name in inputs}==inputs,'input bytes changed'
    for item in sources:assert digest(stage/item['path'])==item['capture_sha256']
    result=dict(status='passed',runtime_sha=PIN,modulus=str(MODULUS),inputs=inputs,
        runtime_manifest_sha256=digest(pinned),runtime_sources=sources,diagnostic_overlays=recipe['changes'],
        raw_graph_identity=source,selected_raw_node_matches=8,selected_raw_constant_matches=3,
        selected_raw_assertion_matches=1,selected_raw_index_body_matches=len(seen),
        complete_ordered_row_recomparison=comparison,adapter=framing,
        pilot_outputs=dict(local_indices=[13],scope='chosen pilot output, not captured runtime output'),
        attribution='observed capture indices and DB origin/certificate ordinals retained',
        clean_source_verifier_vk_correspondence='OPEN',full_transfer='OPEN')
    target=OUT/'provenance-successor01.json';assert not target.exists()
    target.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(status='passed',rows=len(seen),full_recomparison=200770)),flush=True)
if sys.argv[1:]==['--worker']:worker();sys.exit(0)
receipt=OUT/'provenance-guarded01.json';log=OUT/'provenance-guarded01.log'
assert not receipt.exists() and not log.exists()
command=[str(ROOT/'work/parent-full-program/venv/bin/python'),str(Path(__file__).resolve()),'--worker']
started=time.monotonic();peak=0;reason=None
with log.open('w') as output:
    process=subprocess.Popen(command,cwd=ROOT,env=dict(os.environ),stdout=output,
        stderr=subprocess.STDOUT,start_new_session=True)
    while process.poll() is None:
        rows=subprocess.check_output(['ps','-axo','pgid=,rss='],text=True)
        rss=sum(int(parts[1])*1024 for line in rows.splitlines()
                if len(parts:=line.split())==2 and int(parts[0])==process.pid)
        peak=max(peak,rss)
        free=int(re.search(r'System-wide memory free percentage: (\d+)%',
            subprocess.check_output(['memory_pressure'],text=True)).group(1))
        if time.monotonic()-started>240:reason='time bound'
        elif rss>2*1024**3:reason='RSS bound'
        elif free<15:reason='memory pressure'
        elif shutil.disk_usage(ROOT).free<2*1024**3:reason='disk bound'
        if reason:
            os.killpg(process.pid,signal.SIGTERM)
            try:process.wait(timeout=5)
            except subprocess.TimeoutExpired:os.killpg(process.pid,signal.SIGKILL);process.wait()
            break
        time.sleep(.5)
result=dict(status='passed' if process.returncode==0 else 'failed',exit=process.returncode,
    reason=reason,seconds=time.monotonic()-started,peak_group_rss_bytes=peak,
    timeout_seconds=240,rss_limit_bytes=2*1024**3,source_sha256=digest(Path(__file__).resolve()),
    log_sha256=digest(log))
receipt.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
sys.exit(0 if result['status']=='passed' else 1)
