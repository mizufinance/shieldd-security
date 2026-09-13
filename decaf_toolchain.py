"""Select reviewed native artifacts without treating hashes as portable."""
import platform
import re
from pathlib import Path


def native_host():
    system, machine = platform.system(), platform.machine().lower()
    hosts = {
        ("Darwin", "arm64"): "aarch64-apple-darwin",
        ("Linux", "x86_64"): "x86_64-unknown-linux-gnu",
    }
    try:
        return hosts[system, machine]
    except KeyError:
        raise ValueError(f"unsupported native proof host: {system}/{machine}") from None


def native_artifact(config, name):
    """Fail closed unless this host has an explicit artifact identity."""
    host = native_host()
    if name not in ("fiat", "hax", "goose"):
        raise ValueError("unknown native proof tool: " + name)
    build = config.get("native_builds", {}).get(host, {}).get(name)
    if build is None:
        # Preserve the previously reviewed Mac identities during migration.
        if name == "fiat" and config["fiat"]["native_build"]["host"] == host:
            build = config["fiat"]["native_build"]
        elif name == "hax" and config["hax"]["binary_host"] == host:
            build = {"binary_sha256": config["hax"]["binary_sha256"]}
        elif name == "goose" and host == "aarch64-apple-darwin":
            build = {"binary_sha256": config["perennial"]["goose_sha256"]}
        else:
            raise ValueError(f"no reviewed {name} artifact for {host}")
    hashes = build.get("binary_sha256")
    if name == "hax":
        if not isinstance(hashes, dict) or set(hashes) != {
                "cargo-hax", "driver-hax-frontend-exporter", "hax-engine"}:
            raise ValueError("incomplete hax executable identities")
        values = hashes.values()
    else:
        values = [hashes]
    if any(not isinstance(value, str) or not re.fullmatch(r"[0-9a-f]{64}", value)
           for value in values):
        raise ValueError("invalid native executable identity")
    return dict(build, host=host)


def hax_tool_paths(command, prefix):
    """Match pinned hax's dispatch: driver beside CLI, explicit OCaml engine."""
    cli = Path(command([*prefix, "which", "cargo-hax"]).strip()).resolve(strict=True)
    engine = Path(command([*prefix, "which", "hax-engine"]).strip()).resolve(strict=True)
    return {"cargo-hax": cli,
            "driver-hax-frontend-exporter": cli.with_name("driver-hax-frontend-exporter").resolve(strict=True),
            "hax-engine": engine}
