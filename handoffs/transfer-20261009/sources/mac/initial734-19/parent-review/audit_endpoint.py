"""Read-only independent audit of an existing sealed Mac endpoint."""
import argparse
import hashlib
import json
import re
from pathlib import Path


def require(ok, context):
    if not ok:
        raise ValueError(context)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('packet', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    checked = {}

    def read(pin):
        path = Path(pin['path'])
        with path.open('rb') as handle:
            digest = hashlib.file_digest(handle, 'sha256').hexdigest()
        require(path.stat().st_size == pin['bytes'] and digest == pin['sha256'], str(path))
        checked[str(path)] = pin
        return path.read_bytes()

    envelope = json.loads((args.packet / 'envelope01.json').read_bytes())
    postseal = json.loads((args.packet / 'postseal-guard01.json').read_bytes())
    read(postseal['envelope'])
    require(postseal['producer'] == envelope['producer'], 'producer identity')
    producer = json.loads(read(envelope['producer']))
    for pin in producer.values():
        read(pin)
    read(envelope['protected_original_history'])
    read(envelope['endpoint_receipt'])
    modules = json.loads((args.packet / 'qualified-modules01.json').read_bytes())
    all_recorded = json.loads((args.packet / 'full-audits01.json').read_bytes())
    audited = []
    summaries = []
    for module, entry in modules.items():
        source = read(entry['source']).decode()
        read(entry['object'])
        receipt = json.loads(read(entry['receipt']))
        require(receipt['status'] == 'passed' and receipt['exit'] == 0, module)
        require(receipt['source'] == entry['source'], module + ' source receipt')
        require(entry['object'] in receipt['objects'].values(), module + ' object receipt')
        log = read(receipt['stdout']).decode()
        require(not read(receipt['stderr']).strip(), module + ' stderr')
        require(not re.search(r'\b(?:warning|error|info|trace):|sorryAx', log), module + ' diagnostics')
        names = re.findall(r'(?m)^#check @([A-Za-z0-9_.]+)\s*$', source)
        require(names == [a['name'] for a in receipt['audits']], module + ' declarations')
        reports = re.findall(r"(?m)^'([^']+)' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)", log)
        require(reports == names and len(names) == len(set(names)), module + ' axiom reports')
        cursor = 0
        for name, recorded in zip(names, receipt['audits']):
            pattern = r'(?m)^@?' + re.escape(name) + r'(?:\.\{[^\n]*?\})?\s*:[\s\S]*?^\'' + re.escape(name) + r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
            matches = list(re.finditer(pattern, log))
            require(len(matches) == 1, name)
            match = matches[0]
            require(not log[cursor:match.start()].strip(), name + ' intervening output')
            signature = match.group(0).split("\n'" + name + "' ", 1)[0]
            require(all(not line.strip() or line[0].isspace() for line in signature.splitlines()[1:]), name + ' truncated type')
            axioms = [a.strip() for a in (match.group(1) or '').split(',') if a.strip()]
            require(set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}, name + ' axioms')
            require(signature == recorded['full_type'] and hashlib.sha256(signature.encode()).hexdigest() == recorded['full_type_sha256'], name + ' full type')
            require(axioms == recorded['axioms'], name + ' recorded axioms')
            audited.append(recorded)
            cursor = match.end()
        require(not log[cursor:].strip(), module + ' trailing output')
        summaries.append({'module': module, 'source': entry['source'], 'receipt': entry['receipt'], 'audits': receipt['audits']})
    require(len({a['name'] for a in audited}) == len(audited), 'aggregate duplicate declaration')
    require(sorted(audited, key=lambda a: a['name']) == sorted(all_recorded, key=lambda a: a['name']), 'aggregate audit identity')
    result = {'kind': 'independent parsing of existing sealed source, objects, receipts and compiler output; no Lean replay', 'files_rehashed': len(checked), 'modules': summaries, 'declarations': len(audited), 'full_transfer': 'OPEN', 'full_row_instance': 'OPEN', 'native_correspondence': 'OPEN'}
    with args.output.open('x') as handle:
        json.dump(result, handle, indent=2)
        handle.write('\n')
    print(json.dumps({'modules': len(summaries), 'declarations': len(audited), 'files_rehashed': len(checked)}))


if __name__ == '__main__':
    main()
