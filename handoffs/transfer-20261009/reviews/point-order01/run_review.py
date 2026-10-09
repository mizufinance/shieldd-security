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
prompt=f"Read-only review of final actual concrete base-order packet at {F}, accepted canonical context {C}, and hash-resolved fresh trace/prerequisite sources at {H/'resolved-source'}. Tools Read/Glob/Grep only; no builds/execution/edits. Inspect ConcretePointOrder01.base_order proves addOrderOf the SAME concrete actual Mathlib Point base = Scalar.order using certified Nat.Prime Scalar.order, actual annihilation and nonidentity from ConcretePointTraceComposition01. Check source binding and premises, type assumptions/DecidableEq, group interpretation, exact Scalar.order and dependency hashes. Source is byte-identical to prior actual Opus5.5 reviewed endpoint/order proposal (ed4fc077589188d1351e5333efdb6b3b81ec6513ac489df52f5cb53428c73f16), now actual Windows kernel success. Full trace separate parallel Opus final review, parent independent3144type/axiom audit passed; trace sources are exact hash-resolved context. Parent rehashed189compact files, resolved285source references (38current canonical primality nodes +247trace modules), checked77canonical+247fresh dependency references, reconstructed39actual wrappers after exact existing-audit-strip transform, reparsed all113complete pp.all type/standardaxiom outputs. Thirty-eight prerequisite modules112audits (75theorem37definition) are platformvalidation of accepted numerical primality, zero new primality mathematical credit. Only one new base-order theorem/audit. The first parent wrapper reconstruction incorrectly assumed append-only blocks and refused before credit; repaired auditor now matches exact preserved preparer transformation without changing Lean source or execution. Compact transport preserves originalmanifest40e0cb20... and cites original resource sample SHA; parent inspected worker-derived JSON summaries, not raw resource samples. Guard/admission source hashes verified, admitted physical/commitfree thresholds passed, summaries above stop thresholds, allmodulewall<=240s, disk workerpeak1487296294B<2GiB. Actual executionhead9489b759610e5026b9e5b8cb55ff40022b4e72c8; freeze7ea375d0f6e6f9eb5b3ddcb24341e60fcd734cef. Hash/source identity, currenthost kernel, mathematical theorem and native correspondence remain distinct. Cardinality/Hasse/fullgrouporder/native/full200770rows/fullTransfer OPEN. No Hasse launch, no new negative-control credit, no full certification. Identify actionable mathematical, soundness, provenance or scope defects, or no defect within this exact result."
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
