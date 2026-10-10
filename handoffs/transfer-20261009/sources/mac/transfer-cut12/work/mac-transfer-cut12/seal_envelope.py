"""Append-only post-seal scope, guard and checkpoint envelope."""
import hashlib,json
from pathlib import Path
S=Path(__file__).resolve().parent;R=S.parents[1];O=R/'outputs/mac-transfer-cut12'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
producer=O/'publication-manifest01.json';manifest=json.loads(producer.read_text())
for relative,info in manifest['files'].items():assert sha(R/relative)==info['sha256']
guard=O/'seal-guard01.json';assert json.loads(guard.read_text())['status']=='passed'
summary=json.loads((O/'final-summary01.json').read_text())
scope=O/'scope01.json';assert not scope.exists()
scope.write_text(json.dumps(dict(kernel='61exacttype/standardaxiompairs across7freshmodules;2probes+5successors. 3failedelaborations zero credit. Inherited382receipt/source/object candidates unexecuted.',
 source_semantics='Allsix selected sourceexpressionvalues proved. Cutoutputs c73391+rho10*(c73390+rho23), c73393+rho10*(c73392+rho24).',
 constructor='Cutfirst2productsteps own4columns33796..33799, THEN constructoldjoinedrows throughlaterwrites60778..61929. Exactlyone inheritedsharedcopy. No preservation claim for oldjoinedBASEROWS duringcutconstruction.',
 rows='1157exactselectedrow bodies:4newcutarithmeticrows+1152priorjoined arithmeticrows+onecopy. capture_index_partition is an INDEXLIST theorem plus qualified DATAassociation; notformalrowAt overparentrelation.',
 mathematical_result='SAMEfinalrho hash3 domain18 overhash6 domain17nineinputs with bothcutformulas. Arbitraryrhosatisfyingselectedrows yieldsresult; totalfunctionconstructor extendsarbitrarybase withone/copylink/fournonzero.',
 frame='All22735 originalinputcolumns preserved, copy preserved, exact outside-union columnframe and explicitgap33800..60777.',
 controls='1positive+6productiontwo-productcutcheckerrefusals+1reversecoveragecomponentrefusal; 7pre-executionportablehygienerefusals. Refusals are nottheorems of semanticinequality or wholejoinedguard closure.',
 proof_scope_OPEN=summary['open'],no_additional_kernel_replays=True),indent=2)+'\n')
instructions=S/'PORTABLE_REPLAY.md';assert not instructions.exists()
instructions.write_text('''# Supported Cut12 byte replay

Use Python3 with `-I -B -S`. This performs DATA byte regeneration only, no Lean build.

The shipped input is portable01/cut01.json (14KB qualified projection), portable01/replay-inventory01.json, and the exact CLOSED FLAT portable01/maintained directory. No historical bootstrap, raw capture, composed project, compiler cache, or omitted helper is needed. The inventory binds the executing recipe and all four maintained generators. Directory closure and file hashes are checked before and after every generator.

With TASK_ROOT set to this packet root, invoke the following with fresh output/receipt paths:

```sh
python3 -I -B -S "$TASK_ROOT/portable01/maintained/supported_verify_replay.py" --inventory "$TASK_ROOT/portable01/replay-inventory01.json" --maintained "$TASK_ROOT/portable01/maintained" --descriptor "$TASK_ROOT/portable01/cut01.json" --output "$FRESH_REPLAY_DIR" --receipt "$FRESH_REPLAY_RECEIPT"
```

Verify the producer/envelope and input inventory SHA256 first. All seven generated Lean source bytes must match the accepted hashes. No accepted Lean module should be rerun solely to test portability. Original raw build logs are local-only and omitted from publication selections; compact receipts/full-audit types retain exact hashes and source provenance.
''')
checkpoint=S/'FINAL_CHECKPOINT.md';assert not checkpoint.exists()
checkpoint.write_text(f'''# Cut12 immutable checkpoint

Stage: {S}
Outputs: {O}
Producer: {producer}
ProducerSHA256: {sha(producer)}

7fresh modules/61full-type-and-axiom pairs. 5successors after2admitted probes, within8successor cap. 3failedelaborations retained with ZERO credit; 382inherited observations unexecuted. No new floor marker; previous floor is a separate totalRSS observation, not marginal heap cost.

Actual totals: {summary['total_seconds']:.6f}s named-module wall, {summary['total_source_bytes']}B Lean source, {summary['total_object_bytes']}B olean, max groupRSS{summary['max_RSS_bytes']}B under4GiB. Each -j1/-M2048/LEAN_NUM_THREADS1/900000heartbeats/240s, admission15%memory/2GiBdisk.

Endpoint: TransferCut12Joined01.total_joined_call. Cut2products first, then inherited joined constructor; ONE copy,867steps1157selectedrows. Same finalassignment gives hash3domain18 of hash6domain17nineinputs with both exactcut formulas. All22735sourceinputs,copy,unionoutsideandgap preserved. No oldjoinedbase-row preservation assumption.

Allseven generatedbytes reproduced by CLOSEDflat isolated-I-B-S portable recipe. 7pre-executionhygienerefusals observed. Sourcefreeze02 at review-endpoint02/manifest01.json SHA0f59314a800ee0ef825daedfe9de3c8d521c8cadf02997c134979f0473e9fbd8. ParentactualOpus5.5review/acceptance/publication pending. No more heavy jobs; remain available for review corrections, no new proof task without assignment.

GlobalparentrowAt/full200770relation,native/rawconsumer/callsite,laterconsumers,wholejoinedcandidateguard/fullTransfer OPEN. LatestpublicationACK7ea375d0f6e6f9eb5b3ddcb24341e60fcd734cef. No Git writes/Point retries/acceptedreplays.

Immutable prior probe/parentstage packets must remain untouched. Final envelope references this producer and postseal guard/docs explicitly.
''')
paths=[Path(__file__),guard,O/'seal-guard01.log',scope,instructions,checkpoint]
entries={str(p.relative_to(R)):dict(sha256=sha(p),bytes=p.stat().st_size,publication=p.suffix!='.log') for p in paths}
envelope=O/'seal-envelope01.json';assert not envelope.exists()
envelope.write_text(json.dumps(dict(schema='cut12-post-seal-envelope-v1',producer_manifest_path=str(producer.relative_to(R)),producer_manifest_sha256=sha(producer),entries=entries,scope='Append-only postseal guard/scope/replayinstructions/checkpoint; originalproducerentrybytes rehashed unchanged'),indent=2)+'\n')
print(json.dumps(dict(producer_sha256=sha(producer),envelope_sha256=sha(envelope),entries=len(entries),checkpoint_sha256=sha(checkpoint))))
