from pathlib import Path
import ast,difflib,hashlib,json,shutil,subprocess,re
V=Path(__file__).resolve().parent;W=V.parent.parent;P=W/'mac-assertion-support53-55-kernel-result01'
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
reports=[]
for dirname in ['mac-verifier-links53-source03','mac-assertion-pairs55-source02']:
 s=W/dirname;o=V/'regenerated'/dirname;o.mkdir(parents=True,exist_ok=False)
 for n in ['generate.py','template.lean']:shutil.copyfile(s/n,o/n)
 subprocess.run(['python3','-I','-B','-S',str(o/'generate.py')],check=True)
 originals=list((s/'source-root/ShielddSecurity').glob('*.lean'));assert len(originals)==1
 f=originals[0];assert (o/'source-root/ShielddSecurity'/f.name).read_bytes()==f.read_bytes()
 names=re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)',f.read_text(),re.M)
 reports.append(dict(stage=dirname,source=pin(f),public_declarations=len(names),generator=pin(s/'generate.py'),template=pin(s/'template.lean')))
assert sum(r['public_declarations'] for r in reports)==17
failed=json.loads((P/'failures01.json').read_bytes())
for failure in failed:
 for key in ['source','receipt','stdout','stderr']:
  x=failure[key];assert pin(Path(x['path']))==x
 receipt=json.loads(Path(failure['receipt']['path']).read_bytes())
 assert receipt['status']!='passed' and receipt['exit']!=0 and failure['credit']==0
 assert receipt['cleanup']['clean']
old=W/'mac-assertion-provider50-execution01/maintained/guard.py'
new=W/'mac-assertion-provider50-execution04/maintained/guard.py'
assert pin(old)['sha256']=='aa0d3c1a34182a2408d65956e5bd28f4998307b6e307246f4ee722fe5761141b'
assert pin(new)['sha256']=='a4bca2487c7d7472dc7aa53195f2f194147c210a2f46119f1b3fe905d6a72c84'
a={n.name:n for n in ast.parse(old.read_bytes()).body if isinstance(n,ast.FunctionDef)}
b={n.name:n for n in ast.parse(new.read_bytes()).body if isinstance(n,ast.FunctionDef)}
changed=[n for n in a if ast.dump(a[n])!=ast.dump(b[n])]
assert changed==['fixed_check','execute']
delta=''.join(difflib.unified_diff(old.read_text().splitlines(True),new.read_text().splitlines(True),fromfile='accepted-aa0d3c1a/guard.py',tofile='per-module-a4bca248/guard.py'))
(V/'guard-delta01.diff').write_text(delta)
r=dict(scope='Exact unchanged generation, public census, three failed predecessors, per-module source-root guard adjustment; no Lean build',
 modules=reports,failed_predecessors=len(failed),old_guard=pin(old),new_guard=pin(new),changed_functions=changed,
 guard_delta='Each source root must be canonical, a nonsymlink directory, and contain the exact module source; Lean -R now selects that module root. All memory/thread/time/physical-monitor/process-cleanup/lexical/import policies are unchanged.',
 full_transfer='OPEN')
(V/'generation-guard-review01.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(dict(modules=2,reports=17,failed_predecessors=3,guard_functions=changed)))

