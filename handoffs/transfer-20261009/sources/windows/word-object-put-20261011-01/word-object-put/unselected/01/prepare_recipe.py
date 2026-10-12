from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-word-layer-flatten-20261011-03/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-word-layered-object-read-20261011-02'","UPSTREAM = DIAG / 'transfer-word-layer-flatten-20261011-03'"),
 ("POOL = DIAG / 'transfer-word-layer-flatten-owned-floor-20261011-03'","POOL = DIAG / 'transfer-word-object-put-owned-floor-20261011-01'"),
 ("MODULE = 'TransferWordLayerFlatten01'","MODULE = 'TransferWordObjectPut01'"),
 ('len(current) == 8','len(current) == 4'),
 ('len(records) == 124 and len(audits) == 1059','len(records) == 125 and len(audits) == 1063'),
 ("'objects': 124","'objects': 125"),
 ('len(names) == 4','len(names) == 8'),
 ("'imports': ['ShielddSecurity.TransferWordLayeredObjectRead01']","'imports': ['ShielddSecurity.TransferWordLayerFlatten01']"),
 ("'fresh_audits': 4, 'inherited_audits': 1059","'fresh_audits': 8, 'inherited_audits': 1063"),
 ('WORD_LAYER_FLATTEN_COMPLETE_ONE_HUNDRED_TWENTY_FOUR_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','CHECKED_WORD_OBJECT_PUT_COMPLETE_ONE_HUNDRED_TWENTY_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')]:replace(a,b)
start=s.index('stdout = UPSTREAM / ');end=s.index('assert len(records)',start)
s=s[:start]+s[start:end].replace('TransferWordLayeredObjectRead01','TransferWordLayerFlatten01')+s[end:]
s=s.replace('one-hundred-twenty-four-module','one-hundred-twenty-five-module').replace('1059 inherited full reports','1063 inherited full reports')
scope=('Fixed PendingNullifierBlock checked object_put model observes prior underlying Any type-match before inserting boxed pending fields. Absent/tombstoned or same enum type permits insert; other type panics before mutation. Both Open and Sealed share the expected pending type. Returned update derives exact latest write and frames every other key; supported sealed update derives checked getter from constructed word codec. Eight reports, three definitions and five theorems. Bool denotes expected-type match, not actual native TypeId. Native inner-box TypeId/boxing/Clone/map/locks/compiler/ownership correspondence remains explicit; panic sentinel is non-returning branch outside Rust Result/control. No ancestor replay/native/control/certification credit; full Transfer OPEN.')
start=s.index('\nmapping = ');end=s.index("\nmapping['saturating_capacity_source_shape']",start)
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()), 'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}\nmapping['checked_pending_put_source_shape']=pin(ROOT/'context/checked-pending-put-shape.json')"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index('\n',start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
at=s.index("plan['artifact_policy'] =")
s=s[:at]+"plan['pins'].append(mapping['checked_pending_put_source_shape'])\n"+s[at:]
(ROOT/'prepare.py').write_text(s)
(ROOT/'context').mkdir()
p=Path('C:/src/shieldd-pr160-844389ee/third_party/cnidarium-0.83.0/src/delta.rs');b=p.read_bytes();src=b.decode()
types=src[src.index('    fn object_type('):src.index('    fn object_get<T:')]
put=src[src.index('    fn object_put<T:'):src.index('    fn object_delete(')]
assert types.count('std::any::Any::type_id(&**v)')==2
assert put.index('self.object_type(key)')<put.index('std::any::TypeId::of::<T>()')<put.index('.insert(key, Some(Box::new(value)))')
context={'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a','runtime_source':{'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()},'source_object_type_body':types,'source_object_put_body':put,'scope':'Exact static source association only. TypeId checks inner Any object, not Box type; mismatched type panics before insert. Expected-type Bool abstraction and native Any/TypeId/boxing/Clone/map/lock/compiler semantics remain independent; zero native/control/certification credit.'}
(ROOT/'context/checked-pending-put-shape.json').write_text(json.dumps(context,indent=2,sort_keys=True)+'\n')
print({'checked_pending_object_put':True,'reports':8,'guards_unchanged':True})
