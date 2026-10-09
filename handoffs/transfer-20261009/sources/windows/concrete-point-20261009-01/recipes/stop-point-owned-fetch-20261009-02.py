from pathlib import Path
import json,os,signal
p=Path('/mnt/c/src/shieldd-transfer-handoffs/point-artifact-stage-20261009-02/owned-process.json')
if p.exists():
    data=json.loads(p.read_text());proc=Path('/proc')/str(data['pid'])
    if proc.exists():
        assert (proc/'stat').read_text().split()[21]==data['start_ticks']
        assert data['script'].encode() in (proc/'cmdline').read_bytes()
        assert os.getpgid(data['pid'])==data['pgid']==data['pid']
        os.killpg(data['pgid'],signal.SIGTERM)
print('Owned fetch cleanup checked')
