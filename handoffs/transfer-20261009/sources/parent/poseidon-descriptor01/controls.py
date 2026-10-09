"""Bounded database-fixture controls for the production source-pattern matcher."""
import argparse
import hashlib
import json
import shutil
import sqlite3
import subprocess
import sys
import tempfile
from pathlib import Path

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--database', type=Path, required=True)
p.add_argument('--runtime', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
a = p.parse_args()
matcher = Path(__file__).with_name('match.py')
mutations = {
    'altered_node_operation': "UPDATE nodes SET op='mul' WHERE id=507",
    'altered_input_port': 'UPDATE nodes SET ri=12 WHERE id=503',
    'altered_earlier_node': 'UPDATE nodes SET li=508 WHERE id=511',
    'altered_ark_coefficient': "UPDATE constants SET value='1' WHERE id=178",
    'altered_mds_coefficient': "UPDATE constants SET value='1' WHERE id=182",
    'missing_last_node': 'DELETE FROM nodes WHERE id=5865',
}
results = []
with tempfile.TemporaryDirectory(prefix='poseidon-match-controls-') as temporary:
    root = Path(temporary)
    base = root/'base.sqlite'
    source = sqlite3.connect(a.database.resolve().as_uri()+'?mode=ro', uri=True)
    fixture = sqlite3.connect(base)
    fixture.execute('CREATE TABLE nodes(id INTEGER PRIMARY KEY,op TEXT,lk INT,li INT,rk INT,ri INT)')
    fixture.executemany('INSERT INTO nodes VALUES(?,?,?,?,?,?)', source.execute('SELECT id,op,lk,li,rk,ri FROM nodes WHERE id BETWEEN 503 AND 5865'))
    fixture.execute('CREATE TABLE constants(id INTEGER PRIMARY KEY,value TEXT)')
    fixture.executemany('INSERT INTO constants VALUES(?,?)', source.execute('SELECT id,value FROM constants WHERE id BETWEEN 174 AND 3289'))
    fixture.commit(); fixture.close(); source.close()

    def run(database, output):
        return subprocess.run([sys.executable,str(matcher),'--database',str(database),
                               '--runtime',str(a.runtime),'--output',str(output)],
                              text=True,capture_output=True,timeout=15)
    good = run(base,root/'good.json')
    if good.returncode:
        raise RuntimeError('baseline fixture failed: '+good.stderr)
    descriptor_sha = hashlib.sha256((root/'good.json').read_bytes()).hexdigest()
    for name, mutation in mutations.items():
        changed = root/(name+'.sqlite');shutil.copyfile(base,changed)
        with sqlite3.connect(changed) as connection:
            connection.execute(mutation)
        output = root/(name+'.json')
        result = run(changed,output)
        if result.returncode==0 or 'ValueError:' not in result.stderr or output.exists():
            raise RuntimeError('control did not reject the changed data: '+name)
        reason=result.stderr.strip().splitlines()[-1]
        if not ('node mismatch at' in reason or 'constant mismatch at' in reason):
            raise RuntimeError('unrelated failure cannot earn control credit: '+reason)
        results.append({'name':name,'result':'expected data mismatch','reason':reason})
report={'kind':'Python fixture controls only; no proof or kernel-control credit',
        'matcher_sha256':hashlib.sha256(matcher.read_bytes()).hexdigest(),
        'baseline_descriptor_sha256':descriptor_sha,'controls':results}
a.output.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
