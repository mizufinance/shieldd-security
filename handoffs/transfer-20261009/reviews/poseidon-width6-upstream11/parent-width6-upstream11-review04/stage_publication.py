"""Stage reviewed selected-call checkpoint and append-only provenance successor."""
import hashlib,json,shutil
from datetime import datetime,timezone
from pathlib import Path
H=Path(__file__).resolve().parent;R=H.parents[1];REPO=R/'work/shared-build-handoff';BASE=REPO/'handoffs/transfer-20261009'
O=R/'outputs/mac-poseidon-width6-upstream11';S=R/'work/mac-poseidon-width6-upstream11-portable04'
DEST=BASE/'sources/mac/poseidon-width6-upstream11';REV=BASE/'reviews/poseidon-width6-upstream11';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
d=json.loads((H/'review-disposition01.json').read_text());assert d['accepted_selected_row_checkpoint']
m=json.loads((O/'publication-manifest01.json').read_text());e=json.loads((O/'publication-envelope01.json').read_text());sm=json.loads((S/'successor-manifest04.json').read_text());se=json.loads((S/'successor-envelope04.json').read_text())
assert sha(O/'publication-manifest01.json')==d['original_producer_manifest_sha256'] and sha(O/'publication-envelope01.json')==d['original_envelope_sha256']
assert sha(S/'successor-manifest04.json')==d['successor_manifest_sha256'] and sha(S/'successor-envelope04.json')==d['successor_envelope_sha256']
root=json.loads((R/'work/parent-width6-upstream11-review02/root-closure-audit01.json').read_text());roots=set(root['fresh_reachable']);assert len(roots)==85
assert not DEST.exists() and not REV.exists();DEST.mkdir(parents=True);REV.mkdir(parents=True)
hand=[];generated=[];omitted=[];seen=set();canonical=0
def record(path,maintained=False):
    (hand if maintained else generated).append(str(path.relative_to(REPO)))
for x in m['files']+e['postseal_entries']+sm['files']+se['postseal_entries']:
    if x['path'] in seen:continue
    seen.add(x['path']);p=R/x['path'];assert sha(p)==x['sha256'] and p.stat().st_size==x['bytes']
    if not x.get('publication',True):omitted.append(x);continue
    assert '.lake' not in p.parts and '__pycache__' not in p.parts and p.suffix not in ['.pyc','.log','.olean','.ir']
    q=DEST/x['path'];q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
    category=x.get('category','postseal_checkpoint')
    maintained=category in ['maintained_generator_helper_or_guard','maintained_template','handwritten_helper','postseal_transport_generator'] or (category in ['provenance_successor','failure_source_or_maintained_predecessor'] and (p.suffix=='.py' or p.name.endswith('.lean.txt')))
    record(q,maintained)
    if category in ['generated_instance','handwritten_helper'] and p.stem in roots:
        target=REPO/'circuits/ShielddSecurity'/p.name
        assert not target.exists();shutil.copyfile(p,target);record(target,category=='handwritten_helper');canonical+=1
for p in [O/'publication-manifest01.json',O/'publication-envelope01.json',S/'successor-manifest04.json',S/'successor-envelope04.json']:
    q=DEST/p.relative_to(R);q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q);record(q)
for i in range(1,5):
    origin=R/f'work/parent-width6-upstream11-review{i:02d}';target=REV/origin.name;target.mkdir()
    j=json.loads((origin/'opus55-review.json').read_text());assert not j['is_error'] and 'claude-opus-5-5' in j['modelUsage']
    for p in origin.iterdir():
        if p.is_file() and p.suffix in ['.json','.py']:
            shutil.copyfile(p,target/p.name);record(target/p.name)
    replay=origin/'byte-replay01/replay-result.json'
    if replay.exists():shutil.copyfile(replay,target/'parent-byte-replay-result.json');record(target/'parent-byte-replay-result.json')
plan=R/'work/parent-width6-upstream11-plan01'
for p in plan.iterdir():
    if p.is_file() and p.suffix in ['.json','.py']:
        q=REV/'parent-data'/p.name;q.parent.mkdir(exist_ok=True);shutil.copyfile(p,q);record(q)
readme=DEST/'README.md';readme.write_text('''# Domain-17 two-block width6 call joined to domain-18 width3 call

The checked mathematical endpoint uses one final assignment for both65-round width6 permutations and the accepted65-round width3 call. Nine ordered input LCs, domain17, IV2321 and five-word chunking give hash6 result state1; its exact LC is the domain18 child input. The upstream628-step constructor satisfies837selected rows38040..38875+copy200769. The joined865-step run satisfies1153rows38040..39191+copy, with one shared copy. It preserves all22735original inputs at3+input, copy, the two external cut LCs at columns33796/33798, and every column outside writes60778..61929. Earlier constructed rows remain satisfied through checked support and write separation. Field/CharP fixedp, unit0=1,4≠0 and copy-link premises are explicit.

All87fresh executions passed496complete declaration type/axiom audits. The85root-reachable modules account for491audits; the separate cost-only True marker has1audit and the separate tail leaf probe has4. The85generated-source census excludes two handwritten helpers and includes those two probes, so equal census sizes are distinct sets. Eleven failed Lean attempts, one failed selection qualification and a prelaunch inherited-artifact refusal retain zero credit. Parent independently rehashed386producer+6envelope entries,225inherited source/object/receipt ancestry pairs and29provenance-successor entries; structured full declaration types and axiom lists are included in the reviews. Peak sampled group RSS was2,531,491,840bytes below4GiB.

Four actual Claude Opus5.5 high reviews checked the sources and provenance. The first found generator import ordering; maintained source was fixed and four proof files regenerated and checked. The mathematical endpoint review found no soundness/count defect and narrowed the eight controls to B0R00 syntax and metadata/fixed-LC equality checks. The portable review found an unlisted-module/bytecode gap. A fresh immutable successor closed the directories and requires isolated Python; the final review found no actionable defect. No checked Lean source changed for that provenance repair.

Use the SUCCESSOR route under work/mac-poseidon-width6-upstream11-portable04: invoke its maintained/supported_verify_replay.py with Python -I -B -S, --input portable-input01.json, --maintained its exact18-file maintained directory, --inventory replay-inventory04.json, --helpers its exact2-file helpers directory, and --output-directory a fresh path. Inventory SHA b2b3b987477695a1abec43c2d5675fd1c3c24eea740a4d4be036ea1495eee631; recipe SHA dd382ad3dd8783be7bcff6e045960a9a94466bd162d0a41e9555f6f93a78f14a. Parent reproduced85generated files1,799,905bytes and independently exercised six DATA refusals, with no bytecode or Lean execution. The original runner/inventory remain historical immutable artifacts; the successor is the supported route. Compact input1,717,578bytes is an exact recursive projection of the locally retained20,452,883-byte qualification descriptor. Full qualification independently checked377prefix nodes,3120round phase ports and837rows; the compact input retains only needed endpoint ports rather than all3120ports.

Capture-index partitions and component row inclusion are kernel facts. Association of captured DB/RowSpool LC bodies to those local source definitions is DATA; no new upstream positional rowAt theorem over a larger parent page or the full200770-row relation is claimed. The inherited width3 page proof remains scoped to38400..39423+copy. Eight controls establish finite first-round syntax/domain/input/fixed-carry/child guard rejections, not semantic inequality or an arbitrary whole-call candidate checker. Native/raw/clean verifier and VK identity, semantics of the external cut formulas, global relation inclusion, later consumers and full Transfer remain OPEN. No final certification refresh occurred. Runtime pin844389ee069e1fb2e576708842d0b389b4d9a44a and all build limits remain unchanged.
''');record(readme)
public={str(p.relative_to(DEST)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(DEST.rglob('*')) if p.is_file()}
p=DEST/'publication-manifest.json';p.write_text(json.dumps({'schema':'parent-reviewed-upstream11-selected-call-publication-v1','files':public,'omitted_local':omitted,'original_producer_manifest_sha256':d['original_producer_manifest_sha256'],'original_envelope_sha256':d['original_envelope_sha256'],'successor_manifest_sha256':d['successor_manifest_sha256'],'successor_envelope_sha256':d['successor_envelope_sha256'],'canonical_new_modules':canonical,'allstage_modules':87,'allstage_audits':496,'root_modules':85,'root_audits':491,'parent_Lean_executions':0,'full_transfer':'OPEN'},indent=2)+'\n');record(p)
p=BASE/'receipts/mac/poseidon-width6-upstream11.json';p.write_text(json.dumps({'schema':'reviewed-upstream11-selected-call-publication-envelope-v1','producer_scope':json.loads((O/'scope01.json').read_text()),'publication_manifest_sha256':sha(DEST/'publication-manifest.json'),'parent_final_disposition':d,'review_path':str(REV.relative_to(BASE)),'full_transfer':'OPEN'},indent=2)+'\n');record(p)
status=BASE/'status/coordinator.json';c=json.loads(status.read_text());c['observed_utc']=datetime.now(timezone.utc).isoformat();c['last_acknowledged_shared_commit']='9489b759610e5026b9e5b8cb55ff40022b4e72c8'
c['actual_results']['poseidon_width6_upstream11']='Parent accepted selected two-block domain17/arity9 hash6 plus domain18 hash3 under samefinalrho:837/1153rows628/865steps,87fresh496audits,85root491; full parent-page position/native/cutsemantics/globalrelationOPEN. Four actualOpus5.5highreviews and immutable isolated byte-replay successor accepted; no final certification.'
c['actual_results']['windows_point_remaining_trace']='Workerreports245modules3138audits and357remainingregularoperations inclfinalcancellation/annihilation passed;2initial/endpointmodules6audits also passed. Parentimmutablepacketreviewpending;38inherited-prime prerequisites+exactorder auditrunning, noHasse.'
c['active_assignments']['mac']='Same retained Sol6.1 high /root/mac_transfer viarelay; upstream11/hygiene04 complete, parentpublishing acceptedcheckpoint; next finite two-product cut plan pending boundedassignment.'
c['active_assignments']['windows']='Same Transfer proof session; chaincompleted at8e55fc6, safely synchronized to9489b75 forinitial/orderbatch; unchangedcaps. Finaltransport/parentreviewpending.'
c['active_assignments']['opus']='Four actualOpus5.5highupstream source/provenance reviews completed; import-order andclosed-directory replay defects fixed at maintainedsource, scope narrowed, finalreview noactionable defect.'
c['publication']='Parent holds push baton; handwritten/helpers/generators separate fromgenerated/evidence. Bothworkers lastcommonACK9489b75. Upstream11 scopedcheckpoint accepted; nofullcertification refresh.'
status.write_text(json.dumps(c,indent=2)+'\n');record(status)
p=BASE/'completion-plan.md';p.write_text(p.read_text()+'''\n\n### Domain-17 nine-input two-block call and same-assignment child join

Parent accepted the finite upstream11 checkpoint:628steps/837rows for both65-round width6 permutations;865steps/1153rows after composing the accepted domain18 width3 call, with one shared copy. All original inputs and external LC support0/33796/33798 are preserved; writes60778..61929. Exact index partitions are checked, but new parent-page positional rowAt/full200770relation inclusion staysOPEN.87fresh executions passed496audits:85root modules491audits plus separate cost marker1 and leaf probe4. Eleven failed Lean attempts retainzero credit. Parent rehashed386+6producer/envelope entries,225inherited dependencies and29provenance-successor entries, reparsed496full declaration/axiom pairs, independently checked fullprefix/row/port DATA and reproduced85generated sources1,799,905bytes. Four actualOpus5.5high reviews found and resolved generator-import ordering and replay-directory closure defects; the final source/provenance scope has no actionable defect. Eight rejection controls coverB0R00 syntax/domain/input/fixed-LC metadata only; an arbitrary whole-call candidate checker remainsOPEN. Supported isolated replay requires-I-B-S and exactclosed maintained/helper inventories. No new Lean run or proof bytes changed for the portable hygiene repair. No final certification refresh.

The same Windows session reports successful245-module3138-audit remaining Point chain and2-module6-audit initial/endpoint batch;357regular+2initial operations are newly worker-qualified, with parentimmutablepacket review pending. Safe synchronization to9489b75 occurred after thechain compiled at8e55fc6. Necessary38-module112-audit Windows primality platform validation is inheritedmathematics, followed by one fresh concrete order audit. Hasse/cardinality/native/globalTransfer remainOPEN. The same Mac worker is preserved via relay; the next six-node/two-product cut-formula join is a DATAproposal until its finite bounded assignment is admitted.
''');record(p)
assert canonical==85 and len(set(hand+generated))==len(hand)+len(generated)
out=H/'publication-staging01.json';assert not out.exists();out.write_text(json.dumps({'handwritten':hand,'generated_evidence':generated,'canonical_modules':canonical,'packet_files':len(public),'omitted_local_files':len(omitted)},indent=2)+'\n');print(json.dumps({'handwritten_paths':len(hand),'generated_evidence_paths':len(generated),'canonical_modules':canonical,'packet_files':len(public),'omitted_local_files':len(omitted)}))
