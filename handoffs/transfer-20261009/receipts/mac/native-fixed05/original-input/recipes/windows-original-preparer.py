from pathlib import Path
import hashlib,importlib.util,json,re,subprocess,sys
P=Path(__file__).resolve().parent
assert len(sys.argv)==3 and sys.argv[1]=='--prepare'
phase=int(sys.argv[2]);assert 0<=phase<9
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
validator=P/'prepare-balance-joint-kernel-92.py'
assert sha(validator)=='28e35c74fe72a824658b20234f57441fd17e35daa537cd7ba037deffd97dbdba'
helper=Path('C:/src/shieldd-formal/circuits/lean_legacy_scalar_audit.py')
assert sha(helper)=='559a933a0f5afc3fab18380db1deef6495a69d4f4dbbb9b9191c49efe713fff3'
spec=importlib.util.spec_from_file_location('fixed_native_trace_legacy_adapter',helper)
h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
body=validator.read_text()
replacements={
 "names=ns['exported_signatures'](read(source))":"names=legacy_adapter.named_signatures(read(source),ns['exported_signatures'],module,expected_source)",
 "assert len(references)==len(print_references)==len(names)":"assert len(references)==len(names) and len(print_references)==len(names)*legacy_adapter.axiom_report_count(module,expected_source)",
 "assert len(used)+len(empty)==1\n                assert not used or set(re.findall(r'[\\w.]+',used[0]))<={'propext','Classical.choice','Quot.sound'}":"legacy_adapter.check_printed_axioms(output,name,legacy_adapter.axiom_report_count(module,expected_source))"}
for before,after in replacements.items():
 assert body.count(before)==1;body=body.replace(before,after)
c={'__name__':'fixed_native_trace_strict_imports','__file__':str(validator),'legacy_adapter':h}
exec(compile(body,str(validator),'exec'),c)
watch=c['watch'];data=c['data'];zero=c['zero']
watch(validator);watch(helper);watch(__file__)
source=P/'native-encryption-fixed-trace-source-2474'
s=data(watch(source/'summary.json','b5a635fa43674d1efae04050a58ddaccdf999b4744325c53f2369aa62309b223'))
assert s['modules']==31 and s['planned_exports']==141 and s['source_only'] and not s['kernel_run']
source_guard=P/'native-encryption-fixed-trace-source-2474-guard'
zero(source_guard/'exit.txt');watch(source_guard/'end.txt');watch(source_guard/'complete.txt')
assert not(source_guard/'stop.txt').exists()
for path,identity in s['inputs'].items():watch(path,identity)
order=s['module_order'];assert len(order)==31 and order[0]=='NativeEncryptionFixedArithmetic'
selected=[order[0]] if phase==0 else order[1+(phase-1)*4:1+phase*4]
assert len(selected)==(1 if phase==0 else 2 if phase==8 else 4)
if phase:
 prior=P/f'narrow-native-encryption-fixed-trace-phase{phase-1:02}-2475-kernel'
 watch(prior/'complete.txt')
 for leaf in prior.iterdir():
  if leaf.is_dir():
   zero(leaf/'exit.txt');watch(leaf/'end.txt');watch(leaf/'audit.json');assert not(leaf/'stop.txt').exists()
stage=P/'windows-jubjub-isolated-05/ShielddSecurity'
external={}
for module in selected:
 path=watch(source/(module+'.lean'),s['files'][module+'.lean'])
 text=path.read_text()
 names=re.findall(r'^#check @([\w.]+)$',text,re.M)
 assert names==re.findall(r'^#print axioms ([\w.]+)$',text,re.M)==s['audits'][module]
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',text)
 for dep in re.findall(r'^import ShielddSecurity\.([\w.]+)$',text,re.M):
  if dep in selected:continue
  if dep in order:
   assert order.index(dep)<order.index(selected[0]), 'only actual earlier phase imports'
   current=watch(stage/(dep+'.lean'))
   expected=watch(source/(dep+'.lean'),s['files'][dep+'.lean'])
   assert current.read_bytes().replace(b'\r\n',b'\n')==expected.read_bytes().replace(b'\r\n',b'\n')
  external[dep]=c['external_leaf'](dep,sha(stage/(dep+'.lean')))
prep=watch(P/'prepare-frozen-source-kernel-original-831.py','07030f50b153a150c94ee17c1592d639e0ed1acf0999ef404eeed3bc04251463')
hardener=watch(P/'harden-fresh-kernel-guards-134.py','38cf95628f48463f4eba69dba0eed2fa9e7cbd39ca09400331dad73354c82193')
out=P/f'native-encryption-fixed-trace-phase{phase:02}-kernel-source-2475'
assert not out.exists();out.mkdir()
for module in selected:(out/(module+'.lean')).write_bytes((source/(module+'.lean')).read_bytes())
(out/'summary.json').write_text(json.dumps(dict(files={module+'.lean':s['files'][module+'.lean'] for module in selected},
 audits={module:len(s['audits'][module]) for module in selected},inputs=c['WATCH'],actual_import_receipts=external,
 source_only=True,kernel_run=False,qualification=False,certification=False,scope=s['scope']),indent=2)+'\n',newline='\n')
name=f'narrow-native-encryption-fixed-trace-phase{phase:02}-2475'
subprocess.run([sys.executable,str(prep),out.name,name],check=True)
subprocess.run([sys.executable,str(hardener),str(P/(name+'-kernel.ps1'))],check=True)
guard=P/(name+'-kernel.ps1')
assert '$taskStage="$taskRoot/windows-jubjub-isolated-05"' in guard.read_text()
assert all(sha(path)==identity for path,identity in c['WATCH'].items())
print(json.dumps(dict(phase=phase,modules=len(selected),exports=sum(len(s['audits'][m]) for m in selected),
 guard_sha256=sha(guard),summary_sha256=sha(out/'summary.json'),kernel_run=False)))
