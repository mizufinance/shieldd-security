"""Atomically publish only successful source-model proofs and compact audits.

Original compiler streams, failed attempts and transport archives stay local.
This does not run Lean, certify native execution or promote a Transfer claim.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, subprocess, tempfile

EXPECTED = {
    'TransferScalarPackChunk01': ('transfer-scalar-pack-chunk-endpoint-20261012-02', 10,
        '1d4d29b12d32b4c014485b146b20ce2941cd662d1301530f9679d4434dda9fb1'),
    'TransferScalarPackWalk01': ('transfer-scalar-pack-walk-endpoint-20261012-06', 7,
        '7e7eec363bba2a120bbcd5fead1c45406544d976798e9d2de3227958aeadecdd'),
    'TransferPolicyPrehashFields01': ('transfer-policy-prehash-fields-endpoint-20261012-02', 6,
        'f1896c1f727f2857de4495a5768a1097f618f366dc0cbed344958187c84d41ea'),
}
RUNTIME = '844389ee069e1fb2e576708842d0b389b4d9a44a'

def require(value, reason):
    if not value:
        raise ValueError(reason)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def run_git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args], text=True).strip()

def parse_reports(data, names):
    remaining = data.decode('utf-8')
    require(not re.search(r'(?im)^(?:/[^\n]*:\d+:\d+:\s*)?(?:warning|error|panic|trace)\s*:|sorryAx', remaining),
            'successful stream contains no diagnostic or admitted proof')
    reports = []
    for name in names:
        pattern = r'^@?' + re.escape(name) + r'\s*:[\s\S]*?^\'' + re.escape(name) + \
                  r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\s*$"
        matches = list(re.finditer(pattern, remaining, re.M))
        require(len(matches) == 1, 'one complete report for ' + name)
        match = matches[0]
        axioms = [] if match.group(1) is None else [x.strip() for x in match.group(1).split(',')]
        require(set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}, 'standard axioms only')
        full_type = match.group(0).split("\n'" + name + "'", 1)[0].strip()
        reports.append(dict(name=name, full_type=full_type,
                            full_type_sha256=digest(full_type.encode()), axioms=axioms))
        remaining = remaining[:match.start()] + remaining[match.end():]
    require(not remaining.strip(), 'all compiler output accounted for')
    return reports

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--runtime', type=Path, required=True)
    parser.add_argument('--selection', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    require(not args.output.exists(), 'fresh immutable output')
    require(run_git(args.runtime, 'rev-parse', 'HEAD') == RUNTIME and
            not run_git(args.runtime, 'status', '--porcelain', '--untracked-files=all'), 'clean exact runtime')
    manifest = json.loads((args.packet/'carrier04-manifest.json').read_bytes())
    for record in manifest['entries']:
        relative = Path(record['path'])
        require(not relative.is_absolute() and '..' not in relative.parts, 'relative carrier member')
        path = args.packet/relative
        require(path.is_file() and not path.is_symlink(), 'ordinary original member')
        data = path.read_bytes()
        require(len(data) == record['bytes'] and digest(data) == record['sha256'], 'carrier identity')
    selection = json.loads(args.selection.read_bytes())['custom_sources']
    ancestors = json.loads((args.packet/'central-ancestor-source-object-identities.json').read_bytes())
    inherited = []
    for record in ancestors:
        name = record['module']
        if name in EXPECTED:
            continue
        selected = selection.get(name)
        require(selected is not None and selected['sha256'] == record['source']['sha256']
                and selected['bytes'] == record['source']['bytes'], 'selected ancestor ' + name)
        inherited.append(dict(module=name, source_sha256=selected['sha256'], source_bytes=selected['bytes'],
                              recorded_windows_object_sha256=record['object']['sha256']))
    modules, sources = [], {}
    for name, (folder_name, count, expected_source) in EXPECTED.items():
        folder = args.packet/folder_name
        source = folder/'source/ShielddSecurity'/f'{name}.lean'
        data = source.read_bytes()
        require(digest(data) == expected_source, 'exact maintained successful source')
        names = ['ShielddSecurity.'+name+'.'+x for x in re.findall(r'^#check @([^\n]+)', data.decode(), re.M)]
        require(len(names) == count, 'complete declaration census')
        events = [json.loads(line) for line in (folder/'qualified/events.jsonl').read_text().splitlines()]
        require(len(events) == 2 and events[0]['event'] == 'attempt_started'
                and events[1]['event'] == 'attempt_finished' and events[1]['module'] == name, 'terminal original run')
        result = events[1]['result']
        require(result['status'] == 'passed' and result['command'][1:3] == ['-j1', '-M1536'], 'bounded original success')
        report = folder/'reports'/f'fresh-{count}-complete-declarations.txt'
        report_data = report.read_bytes()
        require(len(report_data) == result['stdout']['bytes']
                and digest(report_data) == result['stdout']['sha256'], 'original successful output identity')
        audits = parse_reports(report_data, names)
        require(set(result['audits']) == set(names), 'exact recorded audit census')
        for audit in audits:
            recorded = result['audits'][audit['name']]
            require(audit['full_type_sha256'] == recorded['full_type_sha256']
                    and set(audit['axioms']) == set(recorded['axioms']), 'recorded type/axiom agreement')
        for runtime_copy in (folder/'runtime').rglob('*'):
            if runtime_copy.is_file():
                relative = runtime_copy.relative_to(folder/'runtime')
                require(runtime_copy.read_bytes() == (args.runtime/relative).read_bytes(), 'locked runtime source copy')
        scope = json.loads((folder/'qualified/review.json').read_bytes())['scope']
        modules.append(dict(module=name, source_sha256=expected_source, source_bytes=len(data),
            origin='Retained Windows kernel execution; independently checked source and complete report bytes',
            command=result['command'], seconds=result['seconds'], peak_rss_bytes=result['peak_rss_bytes'],
            recorded_objects=result['objects'], original_successful_stdout_sha256=result['stdout']['sha256'],
            original_successful_events_sha256=digest((folder/'qualified/events.jsonl').read_bytes()),
            full_declarations=audits, scope=scope, native_execution_credit=0))
        sources[name] = data
    require(run_git(args.runtime, 'rev-parse', 'HEAD') == RUNTIME and
            not run_git(args.runtime, 'status', '--porcelain', '--untracked-files=all'), 'runtime unchanged')
    evidence = dict(kind='Reviewed successful source-model packing and prehash proofs', runtime_sha=RUNTIME,
        lean_toolchain='leanprover/lean4:v4.30.0', modules=modules, inherited_source_identities=inherited,
        kernel_execution='Original bounded Windows executions; no coordinator rerun',
        original_stdout_and_failure_history='Retained locally; not part of this publication',
        native_correspondence='OPEN', full_transfer='OPEN', final_combined_replay='UNRUN', certification=False)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(tempfile.mkdtemp(prefix='.packing-publication-', dir=args.output.parent))
    try:
        target = temporary/'source/ShielddSecurity'
        target.mkdir(parents=True)
        for name, data in sources.items():
            (target/f'{name}.lean').write_bytes(data)
        (temporary/'evidence.json').write_text(json.dumps(evidence, indent=2, sort_keys=True)+'\n')
        os.replace(temporary, args.output)
    finally:
        if temporary.exists():
            shutil.rmtree(temporary)
    print(json.dumps(dict(successful_modules=len(modules), complete_reports=sum(len(m['full_declarations']) for m in modules),
                          output=str(args.output), native_correspondence='OPEN', full_transfer='OPEN')))

if __name__ == '__main__':
    main()
