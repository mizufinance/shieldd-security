"""Publish the successful square-root final-check model and complete audits."""
from pathlib import Path
import argparse, hashlib, importlib.util, json, os, re, shutil, subprocess, tempfile

def sha(data):
    return hashlib.sha256(data).hexdigest()

def require(value, message):
    if not value:
        raise ValueError(message)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--runtime', type=Path, required=True)
    parser.add_argument('--ff-helper', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    manifest = json.loads((args.packet/'carrier-manifest.json').read_bytes())
    for relative, identity in manifest['files'].items():
        p = Path(relative.replace('\\','/'))
        require(not p.is_absolute() and '..' not in p.parts, 'ordinary relative member')
        data = (args.packet/p).read_bytes()
        require(len(data) == identity['bytes'] and sha(data) == identity['sha256'], 'carrier member identity')
    packet = args.packet/'sqrt-final'
    r = json.loads((packet/'successful-receipt.json').read_bytes())
    git = lambda *a: subprocess.check_output(['git','-C',str(args.runtime),*a],text=True).strip()
    require(git('rev-parse','HEAD') == r['runtime_sha'] and not git('status','--porcelain'), 'clean exact runtime')
    require(r['status'] == 'passed' and r['native_credit'] == 0 and not r['certification'], 'scoped successful receipt')
    source = root/'source/ShielddSecurity/TransferScalarSqrtAcceptance01.lean'
    data = source.read_bytes()
    require(data == (packet/'handwritten/TransferScalarSqrtAcceptance01.lean').read_bytes() and
            len(data) == r['source']['bytes'] and sha(data) == r['source']['sha256'], 'exact successful maintained source')
    require(args.ff_helper.read_bytes() == (packet/'context/ff-0.13.0-helpers.rs').read_bytes(), 'locked local helper matches reviewed source')
    report = (packet/'full-types-and-axioms.txt').read_bytes()
    require(len(report) == r['full_types_and_axioms']['bytes'] and sha(report) == r['full_types_and_axioms']['sha256'], 'successful original output')
    spec = importlib.util.spec_from_file_location('reports',root.parent/'native-packing/refresh.py')
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    names = ['ShielddSecurity.TransferScalarSqrtAcceptance01.'+s for s in re.findall(r'^#check @(\w+)$',data.decode(),re.M)]
    require(len(names) == 6, 'six complete declarations')
    audits = helper.parse_reports(report,names)
    for audit in audits:
        require({k:audit[k] for k in ['axioms','full_type_sha256']} == r['audits'][audit['name']], 'independent type/axiom audit')
    require(set(names) == set(r['audits']), 'exact receipt census')
    require(not args.output.exists(), 'fresh immutable output')
    stage = Path(tempfile.mkdtemp(prefix='.refresh-',dir=args.output.parent))
    try:
        target = stage/'source/ShielddSecurity'/source.name
        target.parent.mkdir(parents=True)
        target.write_bytes(data)
        evidence = dict(runtime_sha=r['runtime_sha'],scope=r['scope'],certification=False,native_credit=0,full_transfer='OPEN',
                        audits=audits,source=r['source'],original_successful_receipt_sha256=sha((packet/'successful-receipt.json').read_bytes()),
                        original_stdout=r['full_types_and_axioms'],recorded_windows_object_identity=r['object_identity'],
                        seconds=r['seconds'],peak_rss_bytes=r['peak_rss_bytes'],locked_ff_helper_sha256=sha(args.ff_helper.read_bytes()))
        (stage/'evidence.json').write_text(json.dumps(evidence,indent=2)+'\n')
        os.replace(stage,args.output)
        print(json.dumps(dict(declarations=len(audits),certification=False,native_credit=0)))
    finally:
        if stage.exists():
            shutil.rmtree(stage)

if __name__ == '__main__':
    main()
