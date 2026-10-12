from pathlib import Path
import json,hashlib,re,tarfile,io,difflib
J=Path(__file__).parent;W=J.parent;D=J/'windows-scalar-choice-masks-review01';P=D/'packet01';M='TransferScalarChoiceMasks01';S=P/'source/ShielddSecurity'/(M+'.lean');s=S.read_text()
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
plan=json.loads((P/'qualified/plan.json').read_text());assert all(pin(S)[k]==plan['targets'][0]['source'][k]for k in ['bytes','sha256'])
assert json.loads((D/'endpoint-audit-review01.json').read_text())['fresh_reports']==21
shape=json.loads((P/'context/scalar-choice-masks-shape.json').read_text());crate=P/'context/subtle-2.6.1.crate';lib=P/'context/subtle-2.6.1-lib.rs';lock=P/'runtime/Cargo.lock'
for path,key in [(crate,'subtle_locked_archive'),(lib,'subtle_source_copy'),(lock,'locked_cargo_manifest')]:assert all(pin(path)[k]==shape[key][k]for k in ['bytes','sha256'])
assert lock.read_bytes()==(W/'runtime-snapshot/Cargo.lock').read_bytes()
assert re.search(r'name = "subtle"\s+version = "2.6.1"\s+source = "[^"]+"\s+checksum = "'+pin(crate)['sha256']+'"',lock.read_text())
with tarfile.open(fileobj=io.BytesIO(crate.read_bytes()),mode='r:gz')as t:assert t.extractfile('subtle-2.6.1/src/lib.rs').read()==lib.read_bytes()
rust=lib.read_text();assert 'let mask = -(choice.unwrap_u8() as to_signed_int!($t)) as $t;'in rust and 'a ^ (mask & (a ^ b))'in rust and '*self ^= mask & (*self ^ *other);'in rust and 'debug_assert!((input == 0u8) | (input == 1u8));'in rust and 'Choice(black_box(input))'in rust
scalar=W/'shared-build-handoff/handoffs/transfer-20261009/sources/windows/bounded-native-codec-20261011-01/bounded-native-codec/qualified/context/runtime-library/bls12_381-0.8.0-scalar.rs';assert all(pin(scalar)[k]==shape['scalar_source'][k]for k in ['bytes','sha256']);rs=scalar.read_text()
for v in ['u64::conditional_select(&a.0[0], &b.0[0], choice)','u64::conditional_select(&a.0[3], &b.0[3], choice)','res.conditional_assign(&tmp, (((*e >> i) & 0x1) as u8).into())']:assert v in rs
for v in ['valid : byte.toNat < 2','-(UInt64.ofNat choice.byte.toNat)','a ^^^ (sourceChoiceMask choice &&& (a ^^^ b))','Vector.zipWith (fun x y => sourceWordSelect x y choice) a b','sourceCanonicalSquare current','sourceCanonicalMul squared self','sourcePowLoop (sourceMaskedConstantTimeStep self) exponent','UInt8.ofNat ((word >>> UInt64.ofNat index) &&& 1).toNat','Nat.and_one_is_mod','have maskedCases : masked.toNat = 0 ∨ masked.toNat = 1','rw [sourceMaskedPow, sourcePow, stepSame]']:assert v in s
assert len(re.findall(r'^theorem ',s,re.M))==12 and len(re.findall(r'^def ',s,re.M))==8 and len(re.findall(r'^structure ',s,re.M))==1
contract=lambda x:{m[1]:m[0].split(' :=',1)[0]for m in re.finditer(r'(?m)^theorem ([\w]+)[\s\S]*?(?=^theorem |^def |^set_option pp.all|\Z)',x)}
helper=s[s.index('theorem exact_source_masked_scalar_boolean_selection_equals_the_boolean_branch'):s.index('def sourceMaskedConstantTimeStep')]
audit='set_option pp.all true in\n#check @exact_source_masked_scalar_boolean_selection_equals_the_boolean_branch\n#print axioms exact_source_masked_scalar_boolean_selection_equals_the_boolean_branch\n'
oldbody='  unfold sourceMaskedConstantTimeStep\n  rw [exact_source_masked_scalar_selection_equals_the_whole_canonical_branch]\n  cases bit <;> rfl'
newbody='  exact exact_source_masked_scalar_boolean_selection_equals_the_boolean_branch\n    (sourceCanonicalSquare current) (sourceCanonicalMul (sourceCanonicalSquare current) self) bit'
preparations=[]
for q in sorted((P/'history').iterdir()):
 f=q/'handwritten'/(M+'.lean')
 if not f.exists():continue
 old=f.read_text();assert(q/'project/ShielddSecurity'/(M+'.lean')).read_bytes()==f.read_bytes();cs=contract(s);co=contract(old);assert len(co)==11 and all(cs[k]==v for k,v in co.items())
 normalized=old.replace('import ShielddSecurity.TransferScalarPowBitInteger01','import ShielddSecurity.TransferScalarPowInvariant01').replace('def sourceMaskedConstantTimeStep',helper+'def sourceMaskedConstantTimeStep').replace(oldbody,newbody).replace('set_option pp.all true in\n#check @sourceMaskedConstantTimeStep',audit+'set_option pp.all true in\n#check @sourceMaskedConstantTimeStep');assert normalized==s,q
 item=dict(path=str(q),files=[pin(x)for x in q.rglob('*')if x.is_file()],delta=''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True))))
 if(q/'plan.json').exists():
  op=json.loads((q/'plan.json').read_text());assert op['limits']==plan['limits']and op['pressure_limits']==plan['pressure_limits'];assert(q/'execute_bounded.py').read_bytes()==(P/'qualified/execute_bounded.py').read_bytes()
 if(q/'events.jsonl').exists():
  ev=[json.loads(x)for x in(q/'events.jsonl').read_text().splitlines()];assert len(ev)==2 and ev[-1]['result']['status']=='failed';item['failed_result']=ev[-1]['result'];logs=list(q.rglob('stdout.txt'))
  if item['failed_result']['reason']=='Physical memory pressure':assert not logs;item['stdout']='Genuinely absent original pressure output; no invented log'
  else:assert len(logs)==1 and 'error: (kernel) excessive memory consumption detected'in logs[0].read_text()
 else:item['kernel_result']='No recorded execution result'
 preparations.append(item)
assert len(preparations)==4 and sum('failed_result'in x for x in preparations)==2
assemblies=[dict(path=str(q),files=[pin(x)for x in q.rglob('*')if x.is_file()])for q in(P/'history').iterdir()if'endpoint'in q.name];assert len(assemblies)==4
scope='Exact locked subtle2.6.1 archive matches clean runtime Cargo.lock checksum and source bytes. UInt64 signed-mask select/assign source values correspond to the proved modulo-word XOR/negative-mask model for explicit valid Choice0/1; canonical four-word selection equals the whole operand branch. Actual modeled power shift/mask/cast derives its byte0/1 validity internally. A new reusable Boolean-selection lemma makes whole masked source power equal the previously qualified Boolean power loop without unfolding wide square/multiply bodies. Canonical32-byte serialization follows the original typed-input theorem. All21 original complete public reports comprise one structure,eight definitions,twelve theorems, standard axioms only. Original20-declaration contracts unchanged; only direct import narrowing and proof factoring/additional lemma. Four prior source preparations include two failed attempts: physical pressure with genuinely absent stdout and kernel heap refusal with original diagnostic; other preparations have no recorded execution result. Four assembly preparations, including duplicate Cargo.lock packaging failure, retained without proof replay. Complete original163/1296 consumer branch reused; Root union retains all other accepted prime/inverse/power branches. General callers Choice invariant remains explicit; compiler/volatile barrier/native timing/ABI/ct_eq/all caller origins/private constructor and full Transfer remain OWNED OPEN.'
out=D/'semantic-source-review01.json';assert not out.exists();out.write_text(json.dumps(dict(status='PASSED_SOURCE_HISTORY',fresh_reports=21,source=pin(S),locked_archive=pin(crate),locked_source=pin(lib),exact_runtime_lock=pin(lock),scalar_source=pin(scalar),prior_source_preparations=preparations,prior_assembly_preparations=assemblies,failed_attempts=2,scope=scope,native_execution='UNRUN',full_transfer='OPEN'),indent=2)+'\n');print(json.dumps(dict(status='PASSED_SOURCE_HISTORY',reports=21,failed_attempts=2)))
