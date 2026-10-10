"""Atomically stage an accepted scoped Call14 checkpoint; never write Git or run Lean."""
from pathlib import Path
import argparse,datetime,hashlib,json,os,shutil,subprocess,sys
assert sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site
V=Path(__file__).resolve().parent;R=V.parents[2];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();load=lambda p:json.loads(p.read_bytes())
ap=argparse.ArgumentParser()
for n in ['repository','candidate','disposition','disposition-sha256']:ap.add_argument('--'+n,required=True)
a=ap.parse_args();repo=Path(a.repository).resolve();candidate=Path(a.candidate).resolve();dp=Path(a.disposition).resolve()
assert sha(dp)==a.disposition_sha256;disposition=load(dp)
assert disposition['status']=='accepted_scoped_checkpoint'
assert disposition['final_manifest_sha256']=='a1860ff75f5117b55d5366c5aa96e0a1358830df831118fb0469065f35bbb995'
assert disposition['publication_plan_sha256']==sha(V/'publication-plan03.json')
review=Path(disposition['actual_final_Opus_review']['path']);assert sha(review)==disposition['actual_final_Opus_review']['sha256'];result=load(review)
assert result.get('is_error') is False and 'claude-opus-5-5' in result.get('modelUsage',{})
assert disposition['actual_review_returncode']==0 and disposition['new_Lean_runs_for_parent_review']==0 and disposition['full_Transfer']=='OPEN'
head=subprocess.check_output(['git','--no-optional-locks','rev-parse','HEAD'],cwd=repo,text=True).strip();assert head=='a1962598ad440af95b0237697c7ee6bcc4226fbd'
assert not subprocess.check_output(['git','--no-optional-locks','status','--porcelain'],cwd=repo,text=True)
assert load(repo/'shieldd.lock')['sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
plan=load(V/'publication-plan03.json');B=Path('handoffs/transfer-20261009');D=B/'sources/mac/poseidon-call14';W=B/'reviews/poseidon-call14'
assert not (repo/D).exists() and not (repo/W).exists()
tmp=candidate.with_name(candidate.name+'.pending');assert not tmp.exists() and not candidate.exists();tmp.mkdir(parents=True)
classes={};mapping={}
def write(src,dest,category):
 assert src.is_file() and not src.is_symlink() and not dest.is_absolute() and '..' not in dest.parts
 assert not any(k in dest.parts for k in ['.lake','__pycache__','node_modules']) and src.suffix not in {'.log','.olean','.ir','.ilean','.xz','.pyc','.sqlite'}
 p=tmp/dest;assert not p.exists();p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,p);assert sha(p)==sha(src)
 classes[dest.as_posix()]=category
for src,e in plan['entries'].items():
 p=Path(src);assert sha(p)==e['sha256'] and p.stat().st_size==e['bytes'];dest=Path(e['destination'])
 assert dest.is_relative_to(D) or dest.is_relative_to(W) or dest.is_relative_to(Path('circuits/ShielddSecurity'))
 if dest.is_relative_to(Path('circuits/ShielddSecurity')):assert not (repo/dest).exists()
 write(p,dest,e['commit_class']);mapping[src]={'published_path':dest.as_posix(),'sha256':e['sha256'],'bytes':e['bytes']}
mathreview=Path(disposition['actual_mathematical_Opus_review']['path']);assert sha(mathreview)==disposition['actual_mathematical_Opus_review']['sha256']
mathresult=load(mathreview);assert mathresult.get('is_error') is False and 'claude-opus-5-5' in mathresult.get('modelUsage',{})
for p in [review,mathreview,dp,V/'stage-publication04.py',V/'publication-plan03.json',V/'parent-report-corrections01.json',V/'prepare-review-report-corrections01.py',V/'accept-scoped-checkpoint01.py',V/'inspect-staged-publication01.py',V/'review-final-call14-02.py',V/'review-final-call14-03.py',V/'prepare-staging-source04.py']:
 dest=W/p.name
 if not (tmp/dest).exists():write(p,dest,'maintained' if p.suffix=='.py' else 'generated')
readme=D/'README.md';(tmp/readme).write_text("""# Scoped domain-24 six-input Poseidon constructor

57 successful modules and 398 exact full type/standard axiom audits establish a constructor with 628 steps and 837 selected rows. It contains 627 materialized steps, 836 arithmetic rows and one shared copy row. All six outputs from the first permutation carry into the second; only lane 1 absorbs the sixth original input.

For a field of the pinned characteristic, base0=1, linked base copy and explicit 4!=0, the endpoint is the independently defined width-six Poseidon hash with domain 24 and values at original columns [23,24,30,31,32,33]. The constructor preserves all 22,735 original input columns, copy200692 and every column outside [23472,24308). Prior rows are preserved only given their initial satisfaction and actual a/b support outside that window.

The 13 checker-false controls cover six local R00 syntax checks, four representative tail row/offset identity checks and three fixed metadata checks. They do not establish mutated semantic inequalities or a whole-call mutable candidate guard.

All 60 original launch intents were consumed. Attempts55,56,58 failed and retain zero whole-module or negative-control credit. The 57 accepted modules used 362.77325166806986 total Lean seconds, including failures, under the original 60-attempt/1200-second/512MiB campaign and unchanged host/module limits. Unused time does not permit another attempt. No accepted module was replayed.

The parent independently inspected all 57 raw logs, 398 complete declaration/standard axiom pairs, actual source/object and receipt identities, protected ancestors, import bindings, launch accounting, admission anchors and owned cleanup. Three closed generators independently reproduced all 57 accepted source bytes. Fresh DATA copies remain within the original physical byte cap. Actual Claude Opus5.5 high mathematical review02 and supplemental SOURCE/accounting review03 have separately declared read scopes. The original controller completion charge was 54,235,036 bytes; the parent post-completion census was 54,272,345 bytes; the later source/data replay census was 57,376,472 bytes. Later records do not rewrite the original snapshot. Append-only report corrections and the parent's disposition are recorded separately.

The physical CheckedControls module exports the original Checked01/Controls01 namespaces. Their old unbuilt standalone modules are deliberately absent from the canonical module namespace. The package preserves exact generated bytes and explicit publication mappings. Identical generator-input aliases share one byte file. Historical Proof01/Checked01/Controls01 and accepted-probe input files are provenance under handoffs outside the circuits package; never place generator-inputs on a Lean source path. Original generation recipes retain local artifact identity prerequisites, including the failed58 raw log, so this package makes no standalone original-object replay claim.

Portable result excerpts contain actual receipt/accounting/import identities. Expanded original observations, raw logs, objects, caches, toolchains, DB captures and composed workspaces remain local. Qualified DATA source/row associations do not prove full parent positional rowAt inclusion. Child composition, full captured relation, native callsite/consumer identity, G3/G4/G5/G7, Hasse, cardinality and full Transfer remain OPEN. No final certification refresh ran.
""");classes[readme.as_posix()]='maintained'
publication={'schema':'reviewed-call14-publication-v1','producer_manifest_sha256':disposition['final_manifest_sha256'],'disposition_sha256':sha(dp),'actual_review_sha256':sha(review),'runtime_sha':plan['runtime_sha'],'producer_mapping':mapping,'identical_input_aliases':plan['identical_generator_input_published_aliases'],'local_expanded_record_identities':plan['omitted_local_expanded_records'],'selected_modules':57,'retained_actual_audits':398,'original_ALL_attempts':60,'remaining_original_ALL':0,'source_reproduction_scope':plan['source_reproduction_scope'],'files':{str(p.relative_to(tmp)):{'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(tmp.rglob('*')) if p.is_file()},'new_parent_Lean_runs':0,'final_certification_refresh':False,'full_Transfer':'OPEN'}
pm=D/'publication-manifest01.json';(tmp/pm).write_text(json.dumps(publication,indent=2)+'\n');classes[pm.as_posix()]='generated'
receipt=B/'receipts/mac/poseidon-call14.json';(tmp/receipt).parent.mkdir(parents=True,exist_ok=True);(tmp/receipt).write_text(json.dumps({'schema':'reviewed-call14-publication-envelope-v1','publication_manifest_sha256':sha(tmp/pm),'acceptance':disposition,'full_Transfer':'OPEN'},indent=2)+'\n');classes[receipt.as_posix()]='generated'
co=B/'status/coordinator.json';d=load(repo/co);d['observed_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();d['last_acknowledged_shared_commit']=head
d['active_assignments']['mac']='Same retained Sol6.1 high via former orchestrator relay. Call14 scoped checkpoint accepted; Join15 SOURCE/control proposal BLOCKED by aggregate metadata above its sealed16MiB cap and a first-cache shadow gap; no runtime initialization/admission. Original Call1460 allowance exhausted.'
d['active_assignments']['windows']='Same Transfer proof desktop session. Foreign original3ALL exhausted. Native SOURCE/DATA clarifications remain BLOCKED records; prior actual SOURCE03 reviews recorded, further source reviews reported separately; cumulative native allowance remains UNKNOWN, zero new execution/qualification.'
d['actual_results']['poseidon_call14']='57 successful modules/398 full type-standard axiom audits;628steps837selectedrows, domain24arity6 same-final-assignment hash6. Three failed whole modules0credit;60ALL362.77325166806986s. All inputs/copy/outside frame preserved; prior rows conditional.13 scoped checker-false controls. Parent raw/seal/replay/ownership checks and actual final Opus review recorded. Full parent rowAt/native/global/full Transfer OPEN.'
d['publication']='Serialized parent baton; maintained sources and generated evidence separated. Exact runtime lock; no final certification refresh. Same workers and host limits.'
(tmp/co).parent.mkdir(parents=True,exist_ok=True);(tmp/co).write_text(json.dumps(d,indent=2)+'\n');classes[co.as_posix()]='generated'
cp=B/'completion-plan.md';(tmp/cp).write_text((repo/cp).read_text()+"""
2026-10-10 UTC Call14 scoped checkpoint: 57 successful modules and 398 full type/standard axiom audits; 628 steps/837 selected rows prove the domain24 six-input hash6 on one final assignment and preserve all original inputs, copy and outside write window. Prior-row preservation requires initial satisfaction and actual support outside the window. All60 original launch intents were consumed; failures55/56/58 retain zero credit. Total362.77325166806986 Lean seconds. Three closed generators reproduced every accepted source byte without kernel replay. Parent raw/seal/import/accounting/admission/cleanup inspection and actual Claude Opus5.5 high final review are recorded. Physical Combined exports the old Checked/Controls namespaces; old unbuilt standalone modules are absent. The13 false-checker controls retain their local syntax/row identity/metadata scope. No final certification refresh. Join15 sources/control proposal remain UNRUN and BLOCKED by aggregate metadata above its sealed16MiB bound and a first-cache shadow gap, with no new allowance or admission; foreign3ALLexhausted/nativeTOTALunknown BLOCKED. Full parent rowAt/global relation/G3/G4/G5/G7/Hasse/cardinality/full Transfer OPEN. Same retained workers and build limits persist.
""");classes[cp.as_posix()]='maintained'
files={p.relative_to(tmp).as_posix():{'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(tmp.rglob('*')) if p.is_file()}
staging={'files':files,'maintained':sorted(n for n,c in classes.items() if c=='maintained'),'generated':sorted(n for n,c in classes.items() if c=='generated'),'canonical_modules':57,'base_sha':head,'full_Transfer':'OPEN'}
assert set(files)==set(classes) and not set(staging['maintained'])&set(staging['generated'])
(tmp/'staging01.json').write_text(json.dumps(staging,indent=2)+'\n');os.rename(tmp,candidate)
print(json.dumps({'candidate':str(candidate),'files':len(files),'maintained':len(staging['maintained']),'generated':len(staging['generated']),'canonical_modules':57,'Git_writes':0,'Lean_runs':0}))

