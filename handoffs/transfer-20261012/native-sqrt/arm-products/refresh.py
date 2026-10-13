"""Refresh only the one successful locked ARM64 arithmetic product decomposition source model."""
from pathlib import Path
import argparse,hashlib,json,os,re
def identity(p):
    b=p.read_bytes();return dict(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def verify(p,r):assert identity(p)==r,str(p)
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--repository',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--reports-root',type=Path,required=True);a=ap.parse_args();out=a.output.resolve();assert not out.exists()
manifest=json.loads((root/'successful-manifest.json').read_bytes());paths=json.loads((root/'dependency-repository-review.json').read_bytes());assert not paths['missing']
assert manifest['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a' and manifest['native_credit']==0 and not manifest['certification']
assert len(manifest['modules'])==1 and manifest['successful_declarations']==7
for dep in manifest['dependency_source_identities']:
    found=paths['matched'][dep['module']];data=(a.repository.resolve()/found['path']).read_bytes()
    if found['newline'] in ['LF','CRLF']:data=data.replace(b'\r\n',b'\n')
    if found['newline']=='CRLF':data=data.replace(b'\n',b'\r\n')
    assert len(data)==dep['source']['bytes'] and hashlib.sha256(data).hexdigest()==dep['source']['sha256']
for context in manifest['contexts']:
    verify(root/context['path'].replace('\\','/'),dict(bytes=context['bytes'],sha256=context['sha256']))
pending=out.with_name(out.name+'.pending');pending.mkdir();modules={};reports=[]
for row in manifest['modules']:
    src=root/row['source_path'].replace('\\','/');report=a.reports_root.resolve()/row['report_path'].replace('\\','/');verify(src,row['source']);verify(report,row['report'])
    source=src.read_text();names=re.findall(r'(?m)^#check @([A-Za-z0-9_.]+)\s*$',source);prints=re.findall(r'(?m)^#print axioms ([A-Za-z0-9_.]+)\s*$',source)
    assert names==prints
    names=[n if n.startswith('ShielddSecurity.') else 'ShielddSecurity.'+row['module']+'.'+n for n in names]
    assert set(names)==set(row['audits'])
    assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|implemented_by|extern|native_decide|run_tac|initialize|ofReduceBool|skipKernelTC)\b',source)
    text=report.read_text();left=text;parsed=[]
    assert not re.search(r'(?m)^.*(?:warning|error|panic):|sorryAx|uncaught exception|internal exception',text,re.I)
    for name in names:
        pattern=r'^@?'+re.escape(name)+r'(?:\.\{[^}\n]*\})?\s*:[\s\S]*?^\''+re.escape(name)+r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\s*$"
        matches=list(re.finditer(pattern,left,re.M));assert len(matches)==1,name;mt=matches[0]
        full=mt.group(0).split("\n'"+name+"'",1)[0].strip();axioms=[] if mt.group(1) is None else [x.strip() for x in mt.group(1).split(',') if x.strip()]
        assert set(axioms)<= {'propext','Classical.choice','Quot.sound'} and axioms==row['audits'][name]['axioms']
        sha=hashlib.sha256(full.encode()).hexdigest();assert sha==row['audits'][name]['full_type_sha256']
        parsed.append(dict(name=name,full_type=full,full_type_sha256=sha,axioms=axioms));left=left[:mt.start()]+left[mt.end():]
    assert not left.strip() and row['seconds']<180 and row['peak_rss_bytes']<1536*1024**2
    dest=pending/'source/ShielddSecurity'/src.name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(src.read_bytes())
    modules[row['module']]=dict(source=row['source'],object_identity=row['object_identity'],report=row['report'],plan_identity=row['plan_identity'],runner_identity=row['runner_identity'],seconds=row['seconds'],peak_rss_bytes=row['peak_rss_bytes'],scope=row['scope'],reports=len(parsed))
    reports+=parsed
assert len(reports)==7
evidence=dict(status='passed',packet_id=manifest['packet_id'],runtime_sha=manifest['runtime_sha'],modules=modules,reports=7,complete_types_and_axioms=reports,dependency_sources_verified=len(paths['matched']),source_context=manifest['contexts'],scope=manifest['scope'],manifest=identity(root/'successful-manifest.json'),refresh=identity(Path(__file__)),full_transfer='OPEN',native_credit=0,certification=False)
(pending/'evidence.json').write_text(json.dumps(evidence,indent=2,sort_keys=True)+'\n');os.replace(pending,out);print(json.dumps(dict(status='passed',modules=1,reports=7,dependency_sources_verified=len(paths['matched']))))
