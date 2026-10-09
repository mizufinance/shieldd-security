"""Freeze the measured leaf/extractor and perform read-only Opus review."""
import hashlib,json,re,shutil,subprocess,time
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];STAGE=ROOT/'work/mac-poseidon-width3-rename09';P=STAGE/'project/ShielddSecurity';F=HERE/'frozen'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not F.exists();F.mkdir();pending=['TransferPoseidonWidth3Rename09Leaf01'];seen=set();manifest={}
def copy(src,target):
    target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,target);assert sha(src)==sha(target);manifest[str(target.relative_to(F))]={'source':str(src),'sha256':sha(src),'bytes':src.stat().st_size}
while pending:
    name=pending.pop()
    if name in seen:continue
    seen.add(name);src=P/(name+'.lean');copy(src,F/'ShielddSecurity'/src.name)
    pending.extend(re.findall(r'^import ShielddSecurity\.([A-Za-z0-9_]+)',src.read_text(),re.M))
for name in ['generate_leaf.py','export_second_tail.py','validate_records.py','build_bounded.py']:copy(STAGE/name,F/name)
for name in ['selection-result01.json','selection-guard01.json','leaf-generation01.json','build-TransferPoseidonWidth3Rename09Leaf01-01.json']:copy(ROOT/'outputs/mac-poseidon-width3-rename09'/name,F/name)
copy(HERE/'data-audit01.json',F/'parent-data-audit01.json')
(HERE/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
prompt=f'''Review the immutable frozen packet at {F} read-only. Use Read/Glob/Grep only; do not edit, run code, build or initiate other tools. Review target width3 round2 row/port renaming leaf, its generator, finite qualification exporter, and transitive owned proof helper imports. Prior width6 renaming helpers and width3 template already had scoped reviews; check their use here. Look for mathematical defects, hidden premises, mismatch between qualified original RowSpool data and emitted Lean rows/ports, incomplete or unsound validation, incorrect swap/window bounds or scope inflation. Explicitly distinguish data qualification, exact-row/port equality and injectivity facts from independent recurrence/construction/parent inclusion, which this leaf does NOT yet establish. Import-floor True marker is cost only; raw/native/full Transfer remain OPEN. Build receipt/log re-audits are the parent responsibility. Parent independently compared1025page/copy DB rows,300tail rows,63phase pairs and1548operation pairs; it did not repeat raw-stream qualification. The descriptor itself is large/local and represented by exact SHA a9c0764846ed7c31012f295f3d4f77b952bcff27ce43d4b14c66d92e14ee43ae. Report defects with concrete evidence; otherwise report no defect in this limited scope. Also identify next-task proof obligations without treating them as leaf defects.'''
(HERE/'review-prompt.txt').write_text(prompt+'\n')
start=time.monotonic()
command=['/Users/antoinecyr/.local/bin/claude','--model','claude-opus-5-5','--effort','high','--permission-mode','plan','--tools','Read,Glob,Grep','--strict-mcp-config','--no-session-persistence','--output-format','json','--print',prompt]
with (HERE/'opus55-review.json').open('w') as output,(HERE/'opus55-review.stderr').open('w') as err:
    result=subprocess.run(command,stdout=output,stderr=err,timeout=900)
review=json.loads((HERE/'opus55-review.json').read_text());assert result.returncode==0 and not review['is_error'] and 'claude-opus-5-5' in review['modelUsage']
assert all(sha(F/name)==item['sha256'] for name,item in manifest.items())
print(json.dumps({'status':'review-complete','files':len(manifest),'seconds':time.monotonic()-start,'model':list(review['modelUsage'])}))
