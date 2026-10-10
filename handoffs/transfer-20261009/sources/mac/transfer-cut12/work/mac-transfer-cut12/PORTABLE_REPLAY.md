# Supported Cut12 byte replay

Use Python3 with `-I -B -S`. This performs DATA byte regeneration only, no Lean build.

The shipped input is portable01/cut01.json (14KB qualified projection), portable01/replay-inventory01.json, and the exact CLOSED FLAT portable01/maintained directory. No historical bootstrap, raw capture, composed project, compiler cache, or omitted helper is needed. The inventory binds the executing recipe and all four maintained generators. Directory closure and file hashes are checked before and after every generator.

With TASK_ROOT set to this packet root, invoke the following with fresh output/receipt paths:

```sh
python3 -I -B -S "$TASK_ROOT/portable01/maintained/supported_verify_replay.py" --inventory "$TASK_ROOT/portable01/replay-inventory01.json" --maintained "$TASK_ROOT/portable01/maintained" --descriptor "$TASK_ROOT/portable01/cut01.json" --output "$FRESH_REPLAY_DIR" --receipt "$FRESH_REPLAY_RECEIPT"
```

Verify the producer/envelope and input inventory SHA256 first. All seven generated Lean source bytes must match the accepted hashes. No accepted Lean module should be rerun solely to test portability. Original raw build logs are local-only and omitted from publication selections; compact receipts/full-audit types retain exact hashes and source provenance.
