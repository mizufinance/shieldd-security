"""Append immutable post-seal guard/scope/checkpoint transport identities."""
import hashlib,json,subprocess
from pathlib import Path
S=Path(__file__).resolve().parent;R=S.parents[1];O=R/'outputs/mac-poseidon-width3-call10';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=O/'publication-manifest01.json';m=json.loads(manifest.read_text())
for item in m['files']:assert sha(R/item['path'])==item['sha256'],item['path']
guards=[p for p in O.glob('seal-guard*.json') if json.loads(p.read_text())['status']=='passed'];assert len(guards)==1
guard=guards[0];g=json.loads(guard.read_text());assert sha(guard.with_suffix('.log'))==g['log_sha256'];assert all(sha(S/n)==h for n,h in g['source_guards'].items())
processes=subprocess.check_output(['ps','-axo','pid=,comm='],text=True);heavy=[l.strip() for l in processes.splitlines() if Path(l.split(maxsplit=1)[1]).name in ['lean','lake','cargo']];assert not heavy,heavy
result=json.loads((O/'whole-call-result01.json').read_text())
scope=O/'scope01.json';assert not scope.exists();scope.write_text(json.dumps(dict(proved=['SAME finalrho independent mathematical domain18arity1 hash3','One238step total run satisfies317 selected actual rows including onecopy','Exact selected captureindices38876..39191+200769 and positional rowAt equality','Selected inclusion into1024-row parent page pluscopy','Actual476 earlier rows38400..38875 conditionally preserved','All22735 original witnesses,copy,one cutLC,and outside-write columns preserved'],preconditions=['Field F and CharP F fixed Shared01.p','rho/base0=1 for semantics','4≠0 for compiler identities','basecopy=base0 for constructive row theorem','base satisfies actual476priorpagerows for their preservation'],attribution_correction=result['attribution_successor'],original_accepted_closure_retained=True,controls=result['controls'],full_page_satisfaction_constructed=False,open=result['open'],full_transfer='OPEN'),indent=2)+'\n')
checkpoint=S/'COMPLETED_CHECKPOINT.md';assert not checkpoint.exists();checkpoint.write_text(f'''# Call10 finite whole-call/local-page checkpoint

Heavy lane quiescent. No Git writes. Preserve stage, failures and producer seal.
Stage `{S}`; outputs `{O}`.
Producer manifest `{manifest}` SHA `{sha(manifest)}`.
Review freeze `review-snapshot01/manifest.json` SHA `{result['review_snapshot_sha256']}`.
23 fresh executions of22 distinct modules,187 named full-type/standard-axiom audits; one True import-floor audit is cost-only.10 of187 are a separate regenerated attribution-only AbsorbProof successor; successful original endpoint/import bytes remain unchanged. No inherited execution credit.
19 generated sources byte-replayed in `work/call10-repro01`;18 exactly match originally accepted bytes,one matches separately freshly audited comment-header successor. All explicit portable inputs shipped or required inherited canonical source files with exact guards; no historical bootstrap/read of5.8MB descriptor.
WholeCall10Proof01 SHA cb546c74480ea26ab926f7b662bd24c0fe8e67d4a6359dc3e884049b0a9abe94; Page01 SHA eb3206838006190d8989f6fcdd5a49e526873f79194723514720231723dbade5.
317 selected rows=316 arithmetic38876..39191+copy200769;238steps=237materialized+onecopy. Writes61614..61929. Prior476actual rows38400..38875 preserved only ifbase satisfies them. Later232 page rows39192..39423 remain OPEN. Oneinput6-term cutraw363983; domain18arity1IV274; finalstate1 mathhash3 theorem. Raw365617 association is data only.
Five failed kernel predecessors have zero credit: absorption namespace/subsingleton issues, reservedprefix binder, missingexplicit Shared01 import and symbolic Nat-add rfl finish. All sources/receipts retained. Nine absorption/round productionchecker and five page-selection rejections are exact Bool false statements, not semantic inequalities or exhaustive corruption checks.
Resource guards unchanged: LEAN_NUM_THREADS1,-j1/-M2048,240s/module,4GiB groupRSS,15%memory/2GiBdisk. Source-only parent/Opus review pending final disposition; no accepted replay requested.
Full Transfer/upstream-cut/nativecallsite/consumer identity/full200770relation/clean-source verifierVK/laterconsumer obligations OPEN.
Resume SAME worker /root/mac_transfer. Neworchestrator01a1227a-a87d-7da0-94c8-3d3a8b2992f1 holdsbaton; old/root relay-only. LatestACK8e55fc6550ca6ed0f4b7e81fa122f33c25fac4a0. No Point retry, no active-source reset/Git. Await next assignment after immutable packet acceptance; no further task started.
''')
entries=[]
for p,c,publish in [(guard,'postseal_guard',True),(guard.with_suffix('.log'),'postseal_observation',False),(scope,'precise_scope_and_attribution_disposition',True),(checkpoint,'durable_checkpoint',True),(Path(__file__),'postseal_transport_generator',True)]:entries.append(dict(path=str(p.relative_to(R)),category=c,publication=publish,sha256=sha(p),bytes=p.stat().st_size))
envelope=O/'publication-envelope01.json';assert not envelope.exists();envelope.write_text(json.dumps(dict(producer_manifest=dict(path=str(manifest.relative_to(R)),sha256=sha(manifest)),postseal_entries=entries,heavy_processes=[],producer_entries_unchanged=True,proof_credit_unchanged=True),indent=2)+'\n');print(json.dumps(dict(envelope=str(envelope),sha256=sha(envelope),checkpoint=str(checkpoint),checkpoint_sha256=sha(checkpoint))))
