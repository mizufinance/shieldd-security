"""Stage accepted cut math plus immutable provenance repair and one unbuilt foreign leaf."""
import sys
assert sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site
import datetime,hashlib,json,shutil
from pathlib import Path
H=Path(__file__).resolve().parent;R=H.parents[1];REPO=R/'work/shared-build-handoff';BASE=REPO/'handoffs/transfer-20261009';F=H/'frozen';P=H/'provenance-frozen01'
DEST=BASE/'sources/mac/transfer-cut12';REV=BASE/'reviews/transfer-cut12';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert json.loads((H/'review-disposition01.json').read_bytes())['status']=='accepted_scoped_checkpoint'
assert not DEST.exists() and not REV.exists();DEST.mkdir(parents=True);REV.mkdir(parents=True);sources=[];evidence=[];omitted={}
freeze=json.loads((H/'freeze-manifest01.json').read_bytes())
entries={n:(F/n,x) for n,x in freeze['files'].items()}
succ=json.loads((P/'successor-manifest01.json').read_bytes());binding=json.loads((P/'scope-binding-envelope01.json').read_bytes())
for n,x in {**succ['files'],**binding['entries']}.items():assert n not in entries;entries[n]=(P/n,x)
for n,(src,x) in entries.items():
 assert sha(src)==x['sha256']
 if x.get('publication') is False or n.endswith('.log') or n=='outputs/mac-transfer-cut12/full-audits01.json':
  omitted[n]=dict(**x,parent_disposition='Local raw observation or superseded warning-prefixed structured metadata; zero new credit');continue
 dst=DEST/n;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
 maintained=dst.suffix=='.py' or dst.suffix=='.md'
 (sources if maintained else evidence).append(str(dst.relative_to(REPO)))
for src,n in [(F/'publication-manifest01.json','producer-manifest01.json'),(F/'seal-envelope01.json','producer-envelope01.json'),(P/'successor-manifest01.json','successor-manifest01.json'),(P/'scope-binding-envelope01.json','scope-binding-envelope01.json')]:
 shutil.copyfile(src,DEST/n);evidence.append(str((DEST/n).relative_to(REPO)))
for src in (F/'work/mac-transfer-cut12/project/ShielddSecurity').glob('*.lean'):
 dst=REPO/'circuits/ShielddSecurity'/src.name;assert not dst.exists();shutil.copyfile(src,dst);evidence.append(str(dst.relative_to(REPO)))
for n in ['opus55-review.json','opus55-provenance-review.json','review-disposition01.json','packet-review01.json','successor-review01.json','freeze-manifest01.json','accepted-context-manifest01.json','parent-isolated-replay01.json','structured-type-axiom-audit01.json','audit_packet.py','audit_successor.py','run_review.py','run_provenance_review.py','build_disposition.py','stage_publication.py']:
 src=H/n;dst=REV/n;shutil.copyfile(src,dst);(sources if src.suffix=='.py' else evidence).append(str(dst.relative_to(REPO)))
for n in ['inspect_admission12.py','inspect_probe12.py','parent-admission12.json','parent-probe12-inspection01.json']:
 src=R/'work/parent-upstream-cut-plan01'/n;dst=REV/n;shutil.copyfile(src,dst);(sources if src.suffix=='.py' else evidence).append(str(dst.relative_to(REPO)))
shutil.copyfile(H/'parser-controls-replay01/parser-controls01.json',REV/'parent-parser-controls01.json');evidence.append(str((REV/'parent-parser-controls01.json').relative_to(REPO)))
readme=DEST/'README.md';readme.write_text('''# Two-product cuts joined to the accepted hash constructor

Seven fresh modules and61 exact type/standard axiom pairs establish the two original products and allsix selected expression values, then compose cut construction first with the accepted two-block domain17/arity9 hash6 and domain18 hash3. The joined root reaches3newmodules/39audits plus308exact inherited owned source/object/receipt/canonical identities (311owned total). Probes and checked/control modules are separately compiled facts. The final constructor has867steps and1157selected rows with one shared copy; arbitrary satisfying rho implies the same mathematical hash, and construction preserves all22735original input columns, copy, zero, the outside-union frame and gap33800..60777. It does not assume old joined base rows remain satisfied during cut construction.

The parent independently rehashed83original sealed paths, reparsed61actual full signatures/standard axioms, checked allnew sources/objects/receipts and required inherited identities, and reproduced allseven sources byte-exact under Python-I-B-S with a closed flat five-file inventory. Two actual Claude Opus5.5high reviews found no soundness/construction/generator/provenance defect after precise label correction. Mac limits remain2048MiB,240s,4GiBgroupRSS,900000heartbeats, one lake with LEAN_NUM_THREADS=1. Peak groupRSS was2367930368bytes across seven successful modules;3failed elaborations have zero credit.

The original structured audit artifact included two preceding linter warnings in full_type. It is refused metadata and omitted here while its exact identity remains in the preserved producer manifest. The maintained extractor was repaired in an immutable successor; the parent reproduced all61corrected records exactly. Every original path/byte is unchanged, no Lean replay occurred, and no proof/count changed. One failed extractor attempt has zero credit. Parser controls are two positive scenarios and five refusal scenarios exercising three refusal paths, with no semantic control credit.

The production cut checker has one positive and six refusal facts. The historical reverse_component_rejected theorem is only a mapping-size component refusal (four entries versus five rows), not bidirectional coverage. addChecks is fixed source-syntax DATA independent of candidate rows, not a mutable guard or targeted control. checked_cut_values proves two cut formulas; source_node_values separately proves allsix fixed expressions. Scope addendum supersedes the original labels.

capture_index_partition is an index-list theorem plus qualified DATA association, not a formal parent rowAt theorem. Larger parent-page/full200770relation, native/rawconsumer/callsite identity, later consumers, whole joined candidate checker and full Transfer remain OPEN. No final certification refresh. Raw logs, objects, caches, toolchains and composed workspaces are local only.
''');sources.append(str(readme.relative_to(REPO)))
public={str(p.relative_to(DEST)):dict(sha256=sha(p),bytes=p.stat().st_size) for p in sorted(DEST.rglob('*')) if p.is_file()}
pub=DEST/'publication-manifest.json';pub.write_text(json.dumps(dict(schema='parent-reviewed-cut12-publication-v1',files=public,omitted_local_or_superseded=omitted,original_producer_sha256=sha(F/'publication-manifest01.json'),original_envelope_sha256=sha(F/'seal-envelope01.json'),successor_sha256=sha(P/'successor-manifest01.json'),scope_binding_sha256=sha(P/'scope-binding-envelope01.json'),review_sha256=sha(H/'review-disposition01.json'),all_stage_modules=7,all_stage_audits=61,root_new_modules=3,root_new_audits=39,parent_kernel_runs=0,full_transfer='OPEN'),indent=2)+'\n');evidence.append(str(pub.relative_to(REPO)))
receipt=BASE/'receipts/mac/transfer-cut12.json';receipt.write_text(json.dumps(dict(schema='reviewed-cut12-publication-envelope-v1',publication_sha256=sha(pub),acceptance=json.loads((H/'review-disposition01.json').read_bytes()),full_transfer='OPEN'),indent=2)+'\n');evidence.append(str(receipt.relative_to(REPO)))
# Source-only foreign transport: one unchanged leaf has no owned Hasse imports.
leaf=R/'work/parent-hasse-first-leaf-source01';packet=leaf/'packet';L=BASE/'sources/parent/hasse-port-preflight03'
lm=json.loads((packet/'manifest01.json').read_bytes())
for n,x in lm['files'].items():
 src=packet/n;assert sha(src)==x['sha256'];relative=('prepared/'+n) if n.endswith('.lean') or n=='LICENSE' else 'first-leaf-'+n;dst=L/relative;assert not dst.exists();dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);evidence.append(str(dst.relative_to(REPO)))
for src,n in [(packet/'manifest01.json','first-leaf-manifest01.json'),(leaf/'prepare.py','prepare-first-leaf01.py')]:
 dst=L/n;assert not dst.exists();shutil.copyfile(src,dst);(sources if src.suffix=='.py' else evidence).append(str(dst.relative_to(REPO)))
co=BASE/'status/coordinator.json';d=json.loads(co.read_bytes());d['observed_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();d['last_acknowledged_shared_commit']='d6efed2121c93ac7ada701f6536fdb1afc5fb5f6'
d['active_assignments']['mac']='Same retained Sol6.1 high worker: cut12 accepted after two Opus reviews and immutable structured metadata/scope repair; parent publishing, next bounded plan pending.'
d['active_assignments']['windows']='Same Transfer proof session: ACKclean d6efed2; read-only first Hasse leaf admission plan, three missing exact-pin Mathlib artifact modules being inspected. One unchanged unbuilt foreign leaf pluslicense supplied, no kernel launch.'
d['actual_results']['two_product_cut_join']='Accepted7freshmodules61audits, root3new39audits+308inherited311owned; cutsfirst joined867steps1157rows closes two input cut formulas on samefinalrho. Parent83original+11successor paths unchanged,61actual outputs reparsed,7sourcesbyteexact; twoOpus5.5highreviews noactionable defect after immutable metadata/label repair. Mapping-size component and fixedsource DATA labels explicit.3Leanfailures+1extractorfailure0; parent0Lean. FullparentrowAt/native/later/fullTransferOPEN.'
d['publication']='Parent serial baton; both workers ACKd6efed2. Cut12 maintained sources separate fromgenerated/evidence; single Hasse leaf transport is unbuilt source-only, no compatibility/cardinality credit. No final certification.'
co.write_text(json.dumps(d,indent=2)+'\n');evidence.append(str(co.relative_to(REPO)))
plan=BASE/'completion-plan.md';plan.write_text(plan.read_text()+'''

2026-10-10 UTC cut12 checkpoint: seven fresh modules61audits, root3new/39plus308exact inherited owned modules. Cuts are constructed before the accepted joined hash constructor,867steps/1157selectedrows, preserving all22735inputs/copy/outside-union/gap. Both external cut formulas now derive from original inputs7/20/21; full parent rowAt/native/later/fullTransfer remain OPEN. Two actual Opus5.5highreviews completed; metadata repair preserved83originalpaths and reproduced61corrected records with no kernel replay. Controls are six production refusals, one positive and one mapping-size component refusal; addChecks is fixed syntax DATA only. Same workers/limits persist. Desktop Hasse first-leaf admission was refused because sources and three Mathlib artifact modules were absent; one exact unchanged source plus ApacheLICENSE is now shipped for that single-leaf plan. The other186foreign sources are not required by its owned import closure. No Hasse/compatibility/cardinality proof credit or launch yet.
''');sources.append(str(plan.relative_to(REPO)))
(H/'publication-staging01.json').write_text(json.dumps(dict(sources=sorted(set(sources)),evidence=sorted(set(evidence)),canonical_new_modules=7,packet_files=len(public),omitted=len(omitted),unbuilt_Hasse_leaf=True,full_transfer='OPEN'),indent=2)+'\n')
print(json.dumps(dict(canonical_new_modules=7,maintained_paths=len(set(sources)),evidence_paths=len(set(evidence)),packet_files=len(public),omitted=len(omitted))))
