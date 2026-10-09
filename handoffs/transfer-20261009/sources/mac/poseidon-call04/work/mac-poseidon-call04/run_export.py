import hashlib,json,os,re,shutil,signal,subprocess,sys,time
from pathlib import Path
STAGE=Path(__file__).resolve().parent
ROOT=STAGE.parents[1]
OUT=ROOT/'outputs/mac-poseidon-call04'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=STAGE/'export_rounds.py';identity=sha(source)
guard_sources={name:sha(STAGE/name) for name in ['export_rounds.py','validate_records.py','parent-match.py','parent-descriptor.json']}
command=[str(ROOT/'work/parent-full-program/venv/bin/python'),str(source)]
started=time.monotonic();peak=0;reason=None
attempt=1
while (OUT/f'selection-guard{attempt:02d}.log').exists():attempt+=1
receipt=OUT/f'selection-guard{attempt:02d}.json';log=OUT/f'selection-guard{attempt:02d}.log'
assert not receipt.exists()
with log.open('w') as output:
    process=subprocess.Popen(command,cwd=ROOT,stdout=output,stderr=subprocess.STDOUT,start_new_session=True)
    while process.poll() is None:
        rows=subprocess.check_output(['ps','-axo','pgid=,rss='],text=True)
        rss=sum(int(parts[1])*1024 for line in rows.splitlines() if len(parts:=line.split())==2 and int(parts[0])==process.pid)
        peak=max(peak,rss)
        free=int(re.search(r'System-wide memory free percentage: (\d+)%',subprocess.check_output(['memory_pressure'],text=True)).group(1))
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
result=dict(status='passed' if process.returncode==0 and sha(source)==identity and {name:sha(STAGE/name) for name in guard_sources}==guard_sources else 'failed',exit=process.returncode,
    source_sha256=identity,source_guards=guard_sources,source_guards_after_equal={name:sha(STAGE/name) for name in guard_sources}==guard_sources,reason=reason,seconds=time.monotonic()-started,peak_group_rss_bytes=peak,
    timeout_seconds=240,rss_limit_bytes=2*1024**3,log_sha256=sha(log))
receipt.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
sys.exit(0 if result['status']=='passed' else 1)
