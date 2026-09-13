#!/usr/bin/env python3
"""Build Fiat proof imports from fresh, recursive exact-commit source exports."""
import argparse
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import zipfile

import formal
from decaf_inventory import atomic_json
from decaf_toolchain import native_artifact
from security import bounded_run


def export_tree(repository, revision, destination, env, sources, root=None):
    """Git links are resolved from committed objects, never working-tree metadata."""
    root = destination.resolve() if root is None else root
    git = ["git", "-C", str(repository)]
    tree = subprocess.check_output([*git, "ls-tree", "-rz", revision], env=env)
    expected_blobs = {}
    for entry in tree.split(b"\0"):
        if entry:
            metadata, filename = entry.split(b"\t", 1)
            mode, kind, digest = metadata.decode().split()
            if kind == "blob":
                expected_blobs[filename.decode()] = (mode, digest)
    seen = set()
    raw = subprocess.check_output([*git, "archive", "--format=zip", revision], env=env)
    with zipfile.ZipFile(io.BytesIO(raw)) as archive:
        for entry in archive.infolist():
            path = Path(entry.filename)
            output = destination / path
            if path.is_absolute() or ".." in path.parts or not output.resolve().is_relative_to(root):
                raise ValueError("unsafe source archive entry")
            if entry.is_dir():
                output.mkdir(parents=True, exist_ok=True)
            else:
                output.parent.mkdir(parents=True, exist_ok=True)
                data = archive.read(entry)
                expected_mode, expected_digest = expected_blobs[entry.filename]
                # ZIP permission defaults differ from Git's canonical modes.
                mode = int(expected_mode, 8)
                digest = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
                if digest != expected_digest:
                    raise ValueError("archive content differs from the committed Git blob")
                seen.add(entry.filename)
                if mode & 0o170000 == 0o120000:
                    target = data.decode()
                    if not (output.parent / target).resolve().is_relative_to(root):
                        raise ValueError("source symlink escapes export")
                    output.symlink_to(target)
                else:
                    output.write_bytes(data)
                    output.chmod(mode & 0o777)
    if seen != expected_blobs.keys():
        raise ValueError("source archive omitted committed files")
    sources.append({"repository": str(repository), "revision": revision,
                    "destination": str(destination), "tree": subprocess.check_output(
                        [*git, "rev-parse", revision + "^{tree}"], env=env, text=True).strip()})
    for entry in tree.split(b"\0"):
        if not entry:
            continue
        metadata, name = entry.split(b"\t", 1)
        mode, kind, digest = metadata.decode().split()
        if mode == "160000":
            child = Path(name.decode())
            if child.is_absolute() or ".." in child.parts:
                raise ValueError("unsafe gitlink")
            export_tree(repository / child, digest, destination / child, env, sources, root)


def build_environment():
    # Keep only host discovery and opam configuration, never compiler/make overrides.
    allowed = {"PATH", "HOME", "USER", "LOGNAME", "TMPDIR", "OPAMROOT"}
    return dict({key: value for key, value in os.environ.items() if key in allowed},
                OPAMROOTISOK="1", GIT_NO_REPLACE_OBJECTS="1", GIT_CONFIG_NOSYSTEM="1",
                GIT_CONFIG_GLOBAL=os.devnull, OCAMLPATH="", COQPATH="", LC_ALL="C", TERM="dumb")


def initialize_source_index(source, env):
    # Fiat's make_tactics.sh enumerates committed tactic files using git ls-files.
    # Give the checked archive its own index instead of letting Git discover a
    # parent workspace (or silently return an empty list outside a repository).
    # No build products exist yet. Include ignored committed archive inputs too.
    subprocess.run(["git", "init", "--quiet", str(source)], env=env, check=True)
    subprocess.run(["git", "-C", str(source), "-c", "core.autocrlf=false",
                    "add", "--force", "--all"], env=env, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build-parent", type=Path, default=formal.WORK)
    args = parser.parse_args()
    with formal.exclusive_lock():
        work = formal.WORK / "decaf-fiat-build"
        work.mkdir(exist_ok=True)
        report_path = work / "report.json"
        report = dict(status="blocked", completed=False, full_certification=False, commands=[], sources=[])
        atomic_json(report_path, report)
        env = build_environment()
        def command(argv, cwd, timeout=300):
            argv = list(map(str, argv))
            log = work / f"{len(report['commands']):02}.log"
            report["commands"].append(dict(argv=argv, cwd=str(cwd), log=str(log)))
            atomic_json(report_path, report)
            bounded_run(argv, cwd, env, log, work / "unused", work, timeout)
            return log.read_text()
        try:
            config_path = formal.ROOT / "decaf/proofs/toolchain.json"
            config = json.loads(config_path.read_text())
            native = native_artifact(config, "fiat")
            patch = formal.ROOT / "decaf/proofs/fiat-array-index.patch"
            if formal.file_digest(patch) != native["printer_patch_sha256"]:
                raise ValueError("unreviewed printer patch")
            args.build_parent.mkdir(parents=True, exist_ok=True)
            source = Path(tempfile.mkdtemp(prefix="fiat-proof-source-", dir=args.build_parent)).resolve()
            report.update(source_root=str(source), runner_sha256=formal.file_digest(Path(__file__)),
                          toolchain_sha256=formal.file_digest(config_path), patch_sha256=formal.file_digest(patch))
            export_tree((formal.CACHE / "fiat-crypto").resolve(strict=True), config["fiat"]["revision"],
                        source, env, report["sources"])
            env["GIT_CEILING_DIRECTORIES"] = str(source.parent)
            initialize_source_index(source, env)
            before_patch = formal.file_digest(source / "src/Stringification/Rust.v")
            command(["git", "apply", "--verbose", patch], source)
            if formal.file_digest(source / "src/Stringification/Rust.v") == before_patch:
                raise ValueError("printer patch was not applied")
            # Check the index-dependent generated imports before the heavy job.
            tactics = command([source / "src/Util/make_tactics.sh"], source)
            if sorted(tactics.splitlines()) != sorted((source / "src/Util/Tactics.v").read_text().splitlines()):
                raise ValueError("tactic enumeration differs from the exact source archive")
            # No compiled imports are copied into the fresh export.
            compiled = {".vo", ".vos", ".vok", ".cmxs", ".cma", ".cmo", ".cmx", ".so", ".o"}
            if any(path.suffix in compiled for path in source.rglob("*")):
                raise ValueError("source export contains compiled proof artifacts")
            report["source_files"] = {str(path.relative_to(source)): formal.file_digest(path)
                                      for path in sorted(source.rglob("*")) if path.is_file() and not path.is_symlink()}
            report["source_links"] = {str(path.relative_to(source)): os.readlink(path)
                                      for path in source.rglob("*") if path.is_symlink()}
            prefix = ["opam", "exec", "--switch=decaf-fv", "--"]
            for package in ("rocq-runtime", "rocq-stdlib", "coq-core", "ocaml"):
                version = command(["opam", "list", "--switch=decaf-fv", "--installed", "--columns=version", "--short", package], source).strip()
                if version != config[package]:
                    raise ValueError("unexpected toolchain package: " + package)
            compiler = Path(command([*prefix, "which", "rocq"], source).strip()).resolve(strict=True)
            report["compiler"] = dict(path=str(compiler), sha256=formal.file_digest(compiler))
            report["build_environment"] = env
            report["external_toolchain_boundary"] = "Rocq, OCaml, installed standard library and OS build tools remain trusted"
            report["rocq_version"] = command([*prefix, "rocq", "-v"], source)
            report["packages"] = command(["opam", "list", "--switch=decaf-fv", "--installed", "--columns=name,version", "--short"], source)
            command([*prefix, "make", "-j1", "SKIP_BEDROCK2=1", "COQBIN=" + str(compiler.parent) + "/", "src/PushButtonSynthesis/WordByWordMontgomery.vo",
                     "src/Stringification/Language.vo"], source, timeout=14400)
            changed = [name for name, digest in report["source_files"].items()
                       if not (source / name).is_file() or formal.file_digest(source / name) != digest]
            if changed:
                raise ValueError("build modified exported input sources: " + repr(changed))
            if any(not (source / name).is_symlink() or os.readlink(source / name) != target
                   for name, target in report["source_links"].items()):
                raise ValueError("build modified exported source links")
            report["artifacts"] = {str(path.relative_to(source)): formal.file_digest(path)
                                   for path in sorted(source.rglob("*")) if path.is_file()
                                   and path.suffix in {".vo", ".cmxs", ".cma", ".so"}}
            if "src/PushButtonSynthesis/WordByWordMontgomery.vo" not in report["artifacts"]:
                raise ValueError("missing rebuilt pipeline proof")
            report.update(status="passed", completed=True)
        except (Exception, KeyboardInterrupt) as error:
            report["detail"] = str(error) or "interrupted"
        finally:
            atomic_json(report_path, report)
        print(json.dumps({"status": report["status"], "report": str(report_path)}))
        return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
