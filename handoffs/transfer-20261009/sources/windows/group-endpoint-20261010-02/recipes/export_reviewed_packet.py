"""Transport reviewed sources and structured summaries; exclude raw logs."""
import argparse
import hashlib
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--review", type=Path, required=True)
    parser.add_argument("--destination", type=Path, required=True)
    args = parser.parse_args()
    manifest = json.loads((args.packet / "manifest.json").read_bytes())
    entries, excluded = {}, []

    def put(relative, data, original):
        path = args.destination / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("xb") as handle:
            handle.write(data)
        entries[relative] = {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest(), "original": original}

    for record in manifest["files"]:
        name = record["path"]
        data = (args.packet / name).read_bytes()
        if len(data) != record["bytes"] or hashlib.sha256(data).hexdigest() != record["sha256"]:
            raise ValueError(f"changed capsule input: {name}")
        if name.startswith("audit-output/") or name.endswith("events.jsonl"):
            excluded.append(name)
            continue
        if Path(name).suffix not in {".lean", ".py", ".json"}:
            raise ValueError(f"unexpected transport role: {name}")
        put(name, data, record["original"])
    put("provenance/original-capsule-manifest.json", (args.packet / "manifest.json").read_bytes(), "sealed corrected capsule")
    for name in ["audit_endpoint.py", "audit-result01.json", "endpoint-review.md"]:
        put("parent-review/" + name, (args.review / name).read_bytes(), "independent parent review")
    publication = {
        "kind": "reviewed scoped kernel sources and structured receipt transport; no new replay",
        "original_archive_sha256": "c8b7440fc5341d74a21038564634d698a432d47551d7f0e615eabdcc5b84d176",
        "runtime_sha": manifest["runtime_sha"],
        "prerequisites": manifest["prerequisites"],
        "group": manifest["group"],
        "files": entries,
        "excluded_local_only": excluded,
        "external_inventory": manifest["external_floor"],
        "parent_external_inventory_review": "complete remote inventory digest is recorded; its full contents were not independently rehashed by parent",
        "global_curve_order": "OPEN",
        "native_correspondence": "OPEN",
        "full_relation_instance": "OPEN",
        "full_transfer": "OPEN",
        "portable_executable_recipe_replay": "OPEN; recipe copies preserve original absolute-root provenance",
        "certification_refresh": False,
    }
    with (args.destination / "publication-manifest02.json").open("x") as handle:
        json.dump(publication, handle, indent=2, sort_keys=True)
        handle.write("\n")
    print(json.dumps({"files": len(entries), "bytes": sum(e["bytes"] for e in entries.values()), "excluded_raw_outputs_and_event_logs": len(excluded)}))


if __name__ == "__main__":
    main()
