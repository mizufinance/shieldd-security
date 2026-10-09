"""Read-only actual Point prefix/sample review with independently hashed context."""
import hashlib, json, shutil, subprocess, time
from pathlib import Path
H=Path(__file__).resolve().parent
F=H/'frozen'
REPO=H.parents[1]/'work/shared-build-handoff'
C=H/'canonical-context'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((F/'manifest.json').read_text())
assert all(sha(F/n)==x['sha256'] for n,x in m['files'].items())
assert not C.exists()
C.mkdir()
context={}
for x in json.loads((F/'dependency-resolution.json').read_text()):
    if x['reference_disposition']!='tracked at actual publication HEAD':continue
    src=REPO/x['repository_reference']
    assert sha(src)==x['original_source_sha256']
    dst=C/(x['name']+'.lean')
    shutil.copyfile(src,dst)
    context[dst.name]=sha(dst)
(H/'canonical-context-manifest.json').write_text(json.dumps(context,indent=2)+'\n')
prompt=f'''Review immutable Windows six-module Point sample at {F}, with independently hashed canonical context at {C}, read-only using Read/Glob/Grep. No code execution, builds, or edits. Focus ConcretePointScalarRecurrence01, ConcretePointOperationPilot02, ConcretePointTraceStep003..006 plus maintained generator recipes. Generic integer certificates, actual PointOperationRows, concrete field/point and full StandardCurveModel, and prior prefix-three pilot are accepted context. Verify symbolic even/odd binary scalar recurrence for every AddMonoid, exact candidate step indices, prefixes 7/14/28/57/115, tangent/secant row and inverse certificates, derived output curve membership and actual Mathlib Point equality. Check negative integer quotients, denominator orientation, coordinate transports and predecessor linkage without assuming proposed arithmetic or native correspondence. Two modules from batch04 and four from sample are six fresh modules with 67 declaration type/axiom audits including definitions, proving eight additional regular Point operations; prior two operations are inherited. Two initial infinity operations remain UNRUN. Remaining 357 operations, final scalar endpoint, nonzero/order/cardinality/native/full Transfer are OPEN. Candidate exact canonical data is referenced by hashes and selected records; parent independently rehashed 89 manifest entries, 71 canonical source references and 2 packet-new dependencies, reconstructed all six audit wrappers and reparsed all 67 full pp.all signatures/axiom outputs. Generic recurrence has no axioms; others only standard propext/Classical.choice/Quot.sound. Actual build checkout heads differ from publication HEAD 8e55fc6550ca6ed0f4b7e81fa122f33c25fac4a0 and are recorded separately; imported source hashes agree. Failed parser and universe-suffix auditor batches retain zero credit. Resource caps remain 1536 MiB/240 seconds/300000 heartbeats and one verifier per host. No new negative control credit. Identify actionable mathematical, soundness, generator, or scope defects with evidence, or state no defect within this exact sample scope.'''
(H/'review-prompt.txt').write_text(prompt+'\n')
started=time.monotonic()
cmd=['/Users/antoinecyr/.local/bin/claude','--model','claude-opus-5-5','--effort','high','--permission-mode','plan','--tools','Read,Glob,Grep','--strict-mcp-config','--no-session-persistence','--output-format','json','--print',prompt]
with (H/'opus55-review.json').open('w') as out,(H/'opus55-review.stderr').open('w') as err:
    r=subprocess.run(cmd,stdout=out,stderr=err,timeout=900)
j=json.loads((H/'opus55-review.json').read_text())
assert r.returncode==0 and not j['is_error'] and 'claude-opus-5-5' in j['modelUsage']
assert all(sha(F/n)==x['sha256'] for n,x in m['files'].items())
assert all(sha(C/n)==v for n,v in context.items())
print(json.dumps({'review':'complete','model':list(j['modelUsage']),'seconds':time.monotonic()-started}))
