"""Replay the exact source generator with pinned Rust in an isolated root-owned tree."""
from pathlib import Path
import json,hashlib,shutil,subprocess,re,ast
J=Path(__file__).parent;D=J/'windows-record-read-bound-review01';P=D/'packet01';R=D/'source-replay01'
assert not R.exists();R.mkdir()
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
runtime=P/'runtime/crates/core/component/sct/src/permanent_nullifiers/store.rs'
assert runtime.read_bytes()==(J.parent/'runtime-snapshot'/runtime.relative_to(P/'runtime')).read_bytes()
target=R/'C:/src/shieldd-pr160-844389ee/crates/core/component/sct/src/permanent_nullifiers/store.rs'
target.parent.mkdir(parents=True);shutil.copyfile(runtime,target)
source=P/'generator/generate.py';generator=R/'diagnostics/generator/generate.py';generator.parent.mkdir(parents=True);shutil.copyfile(source,generator)
assert generator.read_bytes()==source.read_bytes()
run=subprocess.run(['python3','-I','-B','-S',str(generator)],cwd=R,capture_output=True,text=True,timeout=30)
assert run.returncode==0,run.stderr
fresh=generator.parent/'generated/TransferRecordReadBound01.lean';original=P/'source/ShielddSecurity/TransferRecordReadBound01.lean'
assert fresh.read_bytes().replace(b'\n',b'\r\n')==original.read_bytes()
expression=re.findall(r'const MAX_RECORD_BYTES: u64 = ([0-9 *]+);',runtime.read_text());assert expression==['4 * 1024 * 1024']
def value(n):
 if isinstance(n,ast.Constant)and type(n.value)is int:return n.value
 assert isinstance(n,ast.BinOp)and isinstance(n.op,ast.Mult);return value(n.left)*value(n.right)
assert value(ast.parse(expression[0],mode='eval').body)==4194304
out=dict(status='PASSED',kind='Independent original unmodified generator byte replay and source constant extraction; no Lean execution',generator=pin(source),runtime=pin(runtime),source=pin(original),isolated_replay_source=pin(fresh),only_encoding_delta='Original Windows text write uses CRLF; exact LF generator output encodes identically',record_byte_limit=4194304,full_transfer='OPEN')
(D/'source-regeneration-review01.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(status='PASSED',module='TransferRecordReadBound01',exact_original_generated_source=True)))
