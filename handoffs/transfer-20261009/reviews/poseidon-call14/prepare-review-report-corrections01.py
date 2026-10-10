"""Append corrections; never alter original observations, reviews or proof evidence."""
from pathlib import Path
import hashlib,json
V=Path(__file__).resolve().parent;F=V.parent/'final-two-result06'
load=lambda p:json.loads(p.read_bytes());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
o=load(F/'final60-observation06.json');p=load(V/'parent-final-RAW-inspection01.json');f=load(V/'fresh-budget-after-DATA-replay01.json');plan=load(V/'publication-plan03.json')
a=o['charged_budget'];b=p['budget'];c=f['budget']
assert (a['charged_source_object_bytes'],a['physical_files'])==(54235036,1324)
assert (b['charged_source_object_bytes'],b['physical_files'])==(54272345,1328)
assert b['charged_source_object_bytes']-a['charged_source_object_bytes']==37309
assert sum(e['bytes'] for e in plan['entries'].values())==9013826
assert 9013826-f['published_selection_bytes']==(V/'fresh-budget-after-DATA-replay01.json').stat().st_size==980
assert all(x['attempts']==60 and abs(x['seconds']-362.77325166806986)<1e-10 for x in [a,b,c])
report=dict(classification='APPEND-ONLY REPORT WORDING CORRECTIONS; no changed proof or original evidence',original_controller_completion=dict(charge=a,observation_sha256=sha(F/'final60-observation06.json')),parent_post_completion_census=dict(charge=b,inspection_sha256=sha(V/'parent-final-RAW-inspection01.json'),later_files=4,later_bytes=37309),parent_after_SOURCE_DATA_replay=dict(charge=c,record_sha256=sha(V/'fresh-budget-after-DATA-replay01.json')),selection_size_explanation=dict(previous_plan02_bytes=f['published_selection_bytes'],current_plan03_bytes=9013826,difference_bytes=980,reason='The 980-byte fresh-budget record was itself added to plan03 after its earlier plan02 observation. Both immutable records remain truthful snapshots.'),explicit_OPEN=['child join','native callsite/consumer identity','whole candidate checker','full parent rowAt','full captured relation','G3','G4','G5','G7','Hasse','cardinality','full Transfer'],old_OPEN_lists_preserved=True,stager_wording='Uses read-only Git HEAD/status queries; performs zero Git writes and zero Lean runs.',historical_module_condition='All historical Proof01/Checked01/Controls01 and accepted-probe inputs are provenance only under handoffs outside the circuits package. Never place generator-inputs on a Lean source path.',actual_review02_sha256=sha(V/'opus55-final-call14-review02.json'),actual_review03_sha256=sha(V/'opus55-final-call14-review03.json'),new_kernel_credit=0,original_attempts_remaining=0,full_Transfer='OPEN')
(V/'parent-report-corrections01.json').open('x').write(json.dumps(report,indent=2)+'\n')
old=V/'stage-publication02.py';oldbytes=old.read_bytes();s=oldbytes.decode()
s=s.replace('never run Git or Lean.','never write Git or run Lean.',1)
needle="for p in [review,dp,V/'stage-publication02.py',V/'publication-plan03.json']:"
assert needle in s
s=s.replace(needle,"mathreview=Path(disposition['actual_mathematical_Opus_review']['path']);assert sha(mathreview)==disposition['actual_mathematical_Opus_review']['sha256']\nmathresult=load(mathreview);assert mathresult.get('is_error') is False and 'claude-opus-5-5' in mathresult.get('modelUsage',{})\nfor p in [review,mathreview,dp,V/'stage-publication03.py',V/'publication-plan03.json',V/'parent-report-corrections01.json',V/'prepare-review-report-corrections01.py']:",1)
needle='Original generation recipes retain local artifact identity prerequisites'
assert needle in s
s=s.replace(needle,'Historical Proof01/Checked01/Controls01 and accepted-probe input files are provenance under handoffs outside the circuits package; never place generator-inputs on a Lean source path. Original generation recipes retain local artifact identity prerequisites',1)
needle='Actual Claude Opus5.5 high final review and the parent\'s disposition are recorded separately.'
assert needle in s
s=s.replace(needle,"Actual Claude Opus5.5 high mathematical review02 and supplemental SOURCE/accounting review03 have separately declared read scopes. The original controller completion charge was 54,235,036 bytes; the parent post-completion census was 54,272,345 bytes; the later source/data replay census was 57,376,472 bytes. Later records do not rewrite the original snapshot. Append-only report corrections and the parent's disposition are recorded separately.",1)
s=s.replace('BLOCKED by aggregate metadata above its unchanged16MiB cap; no runtime initialization/admission.','BLOCKED by aggregate metadata above its sealed16MiB cap and a first-cache shadow gap; no runtime initialization/admission.',1)
s=s.replace('BLOCKED by aggregate metadata above the unchanged16MiB bound, with no new allowance or admission;','BLOCKED by aggregate metadata above its sealed16MiB bound and a first-cache shadow gap, with no new allowance or admission;',1)
target=V/'stage-publication03.py';compile(s,str(target),'exec');target.open('xb').write(s.encode());assert old.read_bytes()==oldbytes
print(json.dumps(dict(report_sha256=sha(V/'parent-report-corrections01.json'),new_factory_sha256=sha(target),actual_factory_invoked=False)))
