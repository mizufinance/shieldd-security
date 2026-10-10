"""Export an existing sealed Join15 endpoint; never run Lean or change proofs.

Original absolute locators remain historical provenance. This transport is not
a portable generator replay or a complete dependency/package certification.
"""
import argparse
import hashlib
import json
from pathlib import Path


def read_record(record):
    path = Path(record["path"])
    data = path.read_bytes()
    if len(data) != record["bytes"] or hashlib.sha256(data).hexdigest() != record["sha256"]:
        raise ValueError(f"changed sealed input: {path}")
    return data


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--campaign-work", type=Path, required=True)
    parser.add_argument("--destination", type=Path, required=True)
    args = parser.parse_args()
    work, destination = args.campaign_work, args.destination
    result = work / "mac-threecall-join15-kernel-result01"
    producer = json.loads((result / "producer-manifest01.json").read_bytes())
    envelope = json.loads((result / "envelope01.json").read_bytes())
    for record in producer["entries"].values():
        read_record(record)
    for record in envelope.values():
        read_record(record)
    qualified = json.loads(read_record(envelope["qualified"]))
    if qualified["fresh_modules"] != 5 or qualified["full_type_standard_axiom_pairs"] != 73:
        raise ValueError("unexpected endpoint")
    entries = {}

    def put(relative, data, origin):
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open("xb") as handle:
            handle.write(data)
        entries[relative] = {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest(), "origin": origin}

    for name, module in qualified["modules"].items():
        put(f"source-root/ShielddSecurity/{name}.lean", read_record(module["source"]), module["source"])
        read_record(module["receipt"])
    maintained_path = work / "mac-threecall-join15-kernel-continuation02/math-maintained-inventory02.json"
    maintained = json.loads(maintained_path.read_bytes())
    for name, record in maintained.items():
        put(f"maintained/{name}", read_record(record), record)
    put("provenance/math-maintained-inventory02.json", maintained_path.read_bytes(), str(maintained_path))
    original_input = work / "mac-poseidon-threecall-join15-source02/generation-input01.json"
    put("provenance/generation-input01.json", original_input.read_bytes(), str(original_input))
    for name in ["producer-manifest01.json", "envelope01.json", "qualified-endpoint01.json", "scope01.json", "postseal-guard01.json"]:
        path = result / name
        put(f"receipts/{name}", path.read_bytes(), str(path))
    review = work / "resumed-orchestration-20261009-01/join15-endpoint-review01.json"
    put("reviews/parent-endpoint-review01.json", review.read_bytes(), str(review))
    payload = {
        "classification": "exact source and sealed existing receipt transport; no new kernel replay",
        "runtime_sha": "844389ee069e1fb2e576708842d0b389b4d9a44a",
        "modules": 5,
        "declaration_audits": 73,
        "entries": entries,
        "excluded": ["raw logs", "objects", "compiler caches", "toolchains", "composed projects"],
        "open": ["portable closed generator replay", "full dependency package integration", "full Transfer"],
    }
    manifest = destination / "manifest15.json"
    with manifest.open("x") as handle:
        json.dump(payload, handle, indent=2, sort_keys=True)
        handle.write("\n")
    print(json.dumps({"files": len(entries), "bytes": sum(e["bytes"] for e in entries.values()), "manifest_sha256": hashlib.sha256(manifest.read_bytes()).hexdigest()}))


if __name__ == "__main__":
    main()
