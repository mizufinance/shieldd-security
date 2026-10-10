"""Independent read-only source/receipt audit of the transported endpoint."""
import argparse
import hashlib
import json
import re
from pathlib import Path


def check(condition, reason):
    if not condition:
        raise ValueError(reason)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("packet", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    root = args.packet
    manifest = json.loads((root / "manifest.json").read_bytes())
    for record in manifest["files"]:
        data = (root / record["path"]).read_bytes()
        check(len(data) == record["bytes"], record["path"])
        check(hashlib.sha256(data).hexdigest() == record["sha256"], record["path"])
    summaries = []
    for spec in manifest['modules']:
        module = spec['module']
        qualification = json.loads((root / ('receipts/' + spec['scope_receipt'] + '.json')).read_bytes())
        entry = next((e for e in qualification.get('qualified', []) if e['module'] == module), None)
        if entry is None:
            entry = {'module': module, 'source': qualification['source'], 'receipt': qualification['receipt']}
        receipt = entry['receipt']
        family = 'semantic/torsion'
        source_path = root / f"handwritten-source/ShielddSecurity/{module}.lean"
        check(hashlib.sha256(source_path.read_bytes()).hexdigest() == entry["source"]["sha256"], module)
        source = source_path.read_text()
        names = re.findall(r"(?m)^#check @([A-Za-z0-9_.]+)\s*$", source)
        check(len(names) == len(set(names)) and set(names) == set(receipt["audits"]), module)
        log_path = root / f"audit-output/{module}.txt"
        check(hashlib.sha256(log_path.read_bytes()).hexdigest() == receipt["stdout"]["sha256"], module)
        log = log_path.read_text()
        check(not re.search(r"\b(?:warning|error|info|trace):|sorryAx", log), module)
        reports = re.findall(r"(?m)^'([^']+)' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)", log)
        check(reports == names, module)
        cursor, audits = 0, []
        for name in names:
            pattern = r"(?m)^@?" + re.escape(name) + r"(?:\.\{[^\n]*?\})?\s*:[\s\S]*?^'" + re.escape(name) + r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
            matches = list(re.finditer(pattern, log))
            check(len(matches) == 1, name)
            match = matches[0]
            check(not log[cursor:match.start()].strip(), name)
            signature = match.group(0).split("\n'" + name + "' ", 1)[0]
            check(all(not line.strip() or line[0].isspace() for line in signature.splitlines()[1:]), name)
            axioms = [a.strip() for a in (match.group(1) or "").split(",") if a.strip()]
            check(set(axioms) <= {"propext", "Classical.choice", "Quot.sound"}, name)
            recorded = receipt["audits"][name]
            check(hashlib.sha256(signature.encode()).hexdigest() == recorded["full_type_sha256"], name)
            check(axioms == recorded["axioms"], name)
            audits.append({"name": name, "full_type": signature, "axioms": axioms})
            cursor = match.end()
        check(not log[cursor:].strip(), module)
        check(receipt["status"] == "passed", module)
        summaries.append({"family": family, "module": module, "source": entry["source"], "audits": audits})
    report = {
        "classification": "independent parent parsing of sealed existing sources and compiler diagnostics; no Lean replay",
        "manifest_files_rehashed": len(manifest["files"]),
        "modules": summaries,
        "declarations": sum(len(m["audits"]) for m in summaries),
        "full_transfer": "OPEN",
        "native_correspondence": "OPEN",
        "global_curve_order": "OPEN",
        "expected_declarations": manifest["type_axiom_pairs"],
        "external_inventory": "remote inventory identities recorded in capsule; complete inventories not independently replayed by parent",
    }
    check(report["declarations"] == manifest["type_axiom_pairs"], "total declarations")
    with args.output.open("x") as handle:
        json.dump(report, handle, indent=2)
        handle.write("\n")
    print(json.dumps({"modules": len(summaries), "declarations": report["declarations"], "files_rehashed": report["manifest_files_rehashed"]}))


if __name__ == "__main__":
    main()
