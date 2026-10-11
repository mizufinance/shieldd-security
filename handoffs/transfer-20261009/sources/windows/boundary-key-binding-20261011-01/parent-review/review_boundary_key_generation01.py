"""Independent pinned literal extraction and isolated original generator replay."""
from pathlib import Path
import hashlib,json,re,subprocess,shutil
J=Path(__file__).parent;W=J.parent;D=J/'windows-boundary-key-binding-review01';P=D/'packet01';G=W/'shared-build-handoff';R=D/'source-replay01';R.mkdir()
sha=lambda b:hashlib.sha256(b).hexdigest()
generation=json.loads((P/'generator/generation.json').read_bytes());again=json.loads((P/'independent-regeneration/generation.json').read_bytes())
for key in ['module','runtime','upstream','generator','literals','fresh_audits','native_credit','certification']:assert generation[key]==again[key]
source=(P/'source/ShielddSecurity/TransferBoundaryKeyBinding01.lean').read_bytes();assert len(source)==generation['source']['bytes']==again['source']['bytes'] and sha(source)==generation['source']['sha256']==again['source']['sha256']
runtime=W/'runtime-snapshot/crates/core/component/sct/src/permanent_nullifiers/store.rs';rust=runtime.read_bytes();assert len(rust)==generation['runtime']['bytes'] and sha(rust)==generation['runtime']['sha256']
upstream=G/'handoffs/transfer-20261009/sources/windows/stage-boundary-source-20261011-01/stage-boundary-source/source/ShielddSecurity/TransferStageBoundarySource01.lean';before=upstream.read_bytes();assert len(before)==generation['upstream']['bytes'] and sha(before)==generation['upstream']['sha256']
generator=(P/'generator/generate.py').read_bytes();assert len(generator)==generation['generator']['bytes'] and sha(generator)==generation['generator']['sha256']
patterns={'boundaryBytes':r'const BOUNDARY_KEY: &str = "([^"\n]+)";','formatKeyBytes':r'const FORMAT_KEY: &str = "([^"\n]+)";','rootBytes':r'const ROOT_KEY: &str = "([^"\n]+)";','legacyGenerationsBytes':r'\.get_raw\("(sct/nullifier_generations/state)"\)','legacySetRootBytes':r'\.get_raw\("(sct/nullifier_set/root)"\)','formatValueBytes':r'const FORMAT: &str = "([^"\n]+)";'}
for key,pattern in patterns.items():
 matches=re.findall(pattern,rust.decode());assert len(matches)==1 and matches[0]==generation['literals'][key]
 code=re.findall(r'^def '+key+r' : Bytes := (\[[^\n]+\])',source.decode(),re.M);assert len(code)==1
 assert json.loads(code[0])==list(matches[0].encode('ascii'))
assert len(set(generation['literals'][k]for k in ['boundaryBytes','formatKeyBytes','rootBytes']))==3
runtime_copy=R/'C:/src/shieldd-pr160-844389ee/crates/core/component/sct/src/permanent_nullifiers/store.rs';runtime_copy.parent.mkdir(parents=True);runtime_copy.write_bytes(rust)
base=R/'diagnostics';old=base/'transfer-stage-boundary-source-20261011-02/handwritten/TransferStageBoundarySource01.lean';old.parent.mkdir(parents=True);old.write_bytes(before)
script=base/'key-source01/generate.py';script.parent.mkdir(parents=True);script.write_bytes(generator)
result=subprocess.run(['python3','-I','-B','-S',str(script)],cwd=R,capture_output=True,text=True,timeout=60);assert result.returncode==0,result.stderr
fresh=(script.parent/'generated/TransferBoundaryKeyBinding01.lean').read_bytes();assert b'\r'not in fresh
assert fresh.replace(b'\n',b'\r\n')==source
out={'status':'PASSED','kind':'Independent literal/data check and exact original maintained generator execution; no Lean execution','original_generator_unmodified':True,'runtime_source_sha256':sha(rust),'upstream_source_sha256':sha(before),'six_ascii_literals_verified':generation['literals'],'original_source_sha256':sha(source),'exact_source_bytes_after_original_Windows_CRLF_encoding':True,'source_bytes':len(source),'scope':'Static source ASCII bytes, three write-key separation and identical generated source only; native key projection/getter/codec/root crypto/ownership remain OPEN','full_transfer':'OPEN'}
(D/'source-regeneration-review01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':'PASSED','six_literals':True,'unmodified_generator':True,'source_bytes':len(source)}))
