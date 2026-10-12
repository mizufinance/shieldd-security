"""Atomic successful-only source/evidence refresh; original logs remain local."""
from pathlib import Path
import argparse, hashlib, importlib.util, json, os, shutil, subprocess, tempfile

def digest(data):
    return hashlib.sha256(data).hexdigest()

def require(value, message):
    if not value:
        raise ValueError(message)

def pinned(record):
    path = Path(record['path'])
    data = path.read_bytes()
    require(len(data) == record['bytes'] and digest(data) == record['sha256'], 'original identity: '+str(path))
    return data

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--receipts', type=Path, required=True)
    parser.add_argument('--runtime', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    templates = json.loads((root/'templates.json').read_bytes())
    git = lambda *a: subprocess.check_output(['git','-C',str(args.runtime),*a],text=True).strip()
    require(git('rev-parse','HEAD') == templates['runtime_sha'] and
            not git('status','--porcelain','--untracked-files=all'), 'clean exact runtime')
    require(not args.output.exists(), 'fresh immutable destination')
    spec = importlib.util.spec_from_file_location('complete_reports',root.parent/'native-packing/refresh.py')
    reports = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(reports)
    inputs = json.loads(args.receipts.read_bytes())
    require(set(inputs) == set(templates['modules']), 'exact successful module census')
    evidence = []
    staging = Path(tempfile.mkdtemp(prefix='.refresh-',dir=args.output.parent))
    try:
        for name, module in templates['modules'].items():
            receipt_path = Path(inputs[name])
            raw_receipt = receipt_path.read_bytes()
            r = json.loads(raw_receipt)
            require(r['module'] == name and r['status'] == 'passed' and r['exit'] == 0 and not r['error'], 'terminal success')
            require(r['cleanup']['clean'] and r['cleanup']['leader_reaped'], 'owned process cleanup')
            require(r['command'][1] == '-j1' and r['command'][2] in {'-M2048','-M3072'}, 'finite single-thread compiler')
            require(r['command'][2] != '-M3072' or name in {'ConcreteFieldParameters280','ConcreteLegalEncoding283'}, 'named heap exception')
            require(r['lean_seconds'] <= 240 and r['peak_group_rss'] <= 4*1024**3, 'time/RSS guard')
            source = module['body']+'\n'+''.join('set_option pp.all true in\n#check @'+a+'\n#print axioms '+a+'\n' for a in module['audits'])
            data = source.encode()
            require(digest(data) == module['source_sha256'] and data == pinned(r['source']), 'generator reproduces qualified source')
            stdout = pinned(r['stdout'])
            require(not pinned(r['stderr']).strip(), 'successful stderr empty')
            audits = reports.parse_reports(stdout,module['audits'])
            require(audits == r['audits'], 'independently parsed complete types and standard axioms')
            objects = []
            for record in r['objects'].values():
                if record is not None:
                    pinned(record)
                    objects.append(dict(bytes=record['bytes'],sha256=record['sha256']))
            p = staging/'source/ShielddSecurity'/f'{name}.lean'
            p.parent.mkdir(parents=True,exist_ok=True)
            p.write_bytes(data)
            evidence.append(dict(module=name,source_sha256=digest(data),source_bytes=len(data),audits=audits,
                                 original_receipt_sha256=digest(raw_receipt),original_stdout_sha256=digest(stdout),
                                 command=r['command'],seconds=r['lean_seconds'],peak_group_rss_bytes=r['peak_group_rss'],
                                 compiled_object_identities=objects))
        result = dict(runtime_sha=templates['runtime_sha'],status='scoped_construction_proofs_passed',
                      certification=False,full_transfer='OPEN',native_credit=0,modules=evidence,
                      scope='Concrete field parameters, exact Boolean/word exclusion certificates, and a compatible shared legal assignment under the explicit premises in legal_completed. No all-row Transfer completeness or soundness claim.',
                      remaining_premises=['actual group model instantiation','legal seed bounds and nonalias meanings','registry semantics and seed correspondence','all remaining assertion truths on the final shared assignment','all observables preserved','full native refinement'])
        (staging/'evidence.json').write_text(json.dumps(result,indent=2)+'\n')
        os.replace(staging,args.output)
        print(json.dumps(dict(modules=len(evidence),audits=sum(len(r['audits']) for r in evidence),certification=False)))
    finally:
        if staging.exists():
            shutil.rmtree(staging)

if __name__ == '__main__':
    main()
