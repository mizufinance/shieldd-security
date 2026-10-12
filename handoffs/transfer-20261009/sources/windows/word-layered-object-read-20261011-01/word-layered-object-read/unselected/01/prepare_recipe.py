from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-pending-saturating-capacity-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-checked-word-publication-20261011-01'","UPSTREAM = DIAG / 'transfer-pending-saturating-capacity-20261011-01'"),
 ("POOL = DIAG / 'transfer-pending-saturating-capacity-owned-floor-20261011-01'","POOL = DIAG / 'transfer-word-layered-object-read-owned-floor-20261011-01'"),
 ("MODULE = 'TransferPendingSaturatingCapacity01'","MODULE = 'TransferWordLayeredObjectRead01'"),
 ('len(current) == 2','len(current) == 5'),
 ('len(records) == 122 and len(audits) == 1046','len(records) == 123 and len(audits) == 1051'),
 ("'objects': 122","'objects': 123"),
 ('len(names) == 5','len(names) == 8'),
 ("'imports': ['ShielddSecurity.TransferCheckedWordPublication01']","'imports': ['ShielddSecurity.TransferPendingSaturatingCapacity01']"),
 ("'fresh_audits': 5, 'inherited_audits': 1046","'fresh_audits': 8, 'inherited_audits': 1051"),
 ('SATURATING_CAPACITY_COMPLETE_ONE_HUNDRED_TWENTY_TWO_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','LAYERED_WORD_GETTER_COMPLETE_ONE_HUNDRED_TWENTY_THREE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')]:replace(a,b)
start=s.index('stdout = UPSTREAM / ');end=s.index('assert len(records)',start)
s=s[:start]+s[start:end].replace('TransferCheckedWordPublication01','TransferPendingSaturatingCapacity01')+s[end:]
s=s.replace('one-hundred-twenty-two-module','one-hundred-twenty-three-module').replace('1046 inherited full reports','1051 inherited full reports')
scope=('Source-shaped checked typed object read traverses live leaf then newest-to-oldest layers before underlying parent. Applied/missing layer or parent yields non-returning panic sentinel; latest tombstone returns empty default and latest wrong type panics without older fallback; map miss alone continues. Symbolic induction derives live stack exact latest-entry selection without supplied selected value or getter success. Eight reports, two definitions and six theorems. Exact getter source shape retained from previous module; native layers/liveness/Any/downcast/Clone/locks/aliasing/time/compiler correspondence and functional delta equivalence remain separate. No ancestor replay/native/control/certification credit; full Transfer OPEN.')
start=s.index('\nmapping = ');end=s.index("\nmapping['saturating_capacity_source_shape']",start)
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()), 'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
replace("mapping['saturating_capacity_source_shape']=pin(ROOT/'context/saturating-capacity-shape.json')", "mapping['saturating_capacity_source_shape']=pin(DIAG/'transfer-pending-saturating-capacity-20261011-01/context/saturating-capacity-shape.json')")
start=s.index("plan['source_repairs'] = ");end=s.index('\n',start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'live_checked_layer_recurrence':True,'reports':8,'guards_unchanged':True})
