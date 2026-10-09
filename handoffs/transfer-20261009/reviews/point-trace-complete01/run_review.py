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
    if x['reference_disposition']!='tracked at freeze HEAD':continue
    src=REPO/x['repository_reference']
    assert sha(src)==x['original_source_sha256']
    dst=C/(x['name']+'.lean')
    shutil.copyfile(src,dst)
    context[dst.name]=sha(dst)
(H/'canonical-context-manifest.json').write_text(json.dumps(context,indent=2)+'\n')
prompt=f'Review the immutable complete concrete Point trace/endpoint packet at {F}, with independently hashed accepted canonical context at {C}. Read only using Read/Glob/Grep; no execution/builds/edits. Prior Point operations, generic scalar recurrence and full concrete StandardCurveModel are accepted context. Inspect all actual new source classes and maintained portable generator, the predecessor links throughout Step007..251, binary prefix recurrence, tangent/secant integer and inverse certificates, actual Mathlib Point equality, derived membership, final vertical inverse/cancellation and exact Scalar.order annihilation. Verify initial infinity operations, nonidentity and endpoint conjunction use the same actual base. In particular detect any hidden assumption of candidate correctness/desired result/native correspondence. Candidate association is DATA only; initial facts are not a separately exported whole graph-link theorem. Parent independently rehashed1287 manifest entries,77 canonical+245 fresh dependency references, reconstructed247 audit wrappers, and re-parsed3144 existing complete pp.all type/axiom outputs; all standard axioms only. Parent checked369 exact candidate-index/slot/case/source associations, and isolated-I-B-S replay reproduced249 sources byte exact. Ten earlier regular operations inherited,359 newly qualified operations including357 remaining regular+2initial,369 total. Counts are declaration audits including definitions, not3144 theorems. Frozen endpoint sources match prior reviewed source-only proposal; final actualStep251 success closes speculative syntax/normalization concern. Review final mathematical/generator/scope claims independently. Chain actually executed at8e55fc6550ca6ed0f4b7e81fa122f33c25fac4a0; endpoint at9489b759610e5026b9e5b8cb55ff40022b4e72c8; freezeACK7ea375d0f6e6f9eb5b3ddcb24341e60fcd734cef must not rewrite these execution heads. Parent inspected8566 resourcesamples with memory above stop thresholds and modulewall<=240s. Unchanged1536MiB heap/300000heartbeats/oneheavyperhost. Composition disk sampledpeak1485558304B below2GiB; firstchain disk peak was not separately sampled, so do not infer a monitored peak. Existing guard/source hashes retained. No new negative-control credit. Exact baseorder theorem is in separate pending packet; cardinality/Hasse/native correspondence/fullrelation/fullTransfer OPEN. Prior final endpoint proposal Opus review found no soundness defect; this is now final actual packet/source/provenance scope review. Isolated replay uses only standard-library imports; executing recipe/generator/verifier/input bound by frozen manifest+parent before/after rehash and receipt inventory, no unlisted local helper/import bootstrap. State actionable mathematical, soundness, generator or provenance defects with evidence, or no defect within the exact scoped result.'
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
