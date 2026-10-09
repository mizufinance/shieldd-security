# M18 binary row framing and complete data comparison

The new `python/circuits/transfer_spool.py` adapts the pinned RowSpool binary format
into the existing bounded relation reader. `transfer_certificate_export.py`
replays the complete selector callback from its completed SQLite database and
verifies the exported framing, ordering, counts and payload hash. Both modules
produce data, not kernel proofs.

The six inherited Python helper files retain their frozen packet identities.
The standalone tests need Python and `blake3`. From this directory:

```
PYTHONPATH=python python -m unittest discover -s python/tests -p 'test_transfer_spool.py'
```

Sixteen focused tests passed in the owned Mac stage. Validly rehashed row-body
mutations first pass the relation reader, then fail exact compiler comparison.
The full local run compared 200,770 original ordered rows and all 758 M17 indexed
row bodies, exported 1,677,169 callback records and verified the complete export.
See `../../../receipts/mac/mac-m18-framing01` relative to this directory.

`publication-manifest01.json` is retained byte-exact from the producer. Its
`sources/<path>` entries resolve under this source directory; its
`receipts/<path>` entries resolve under the corresponding receipt directory.
`run_g1.py` is the exact historical bounded runner and expects the recorded Mac
stage layout and retained capture inputs. It is not the public security CLI.
The SQLite database, raw captures, 1.02 GB gzip, logs and caches remain local.

Arbitrary-assignment semantic soundness, concrete kernel certificates, legal
assertion derivation, total assignment completeness and native/state joins are
separate open gates. These receipts do not certify the publication checkout.
