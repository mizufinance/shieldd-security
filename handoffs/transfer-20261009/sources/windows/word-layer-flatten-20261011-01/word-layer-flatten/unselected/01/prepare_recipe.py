from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-word-layered-object-read-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-pending-saturating-capacity-20261011-01'","UPSTREAM = DIAG / 'transfer-word-layered-object-read-20261011-02'"),
 ("POOL = DIAG / 'transfer-word-layered-object-read-owned-floor-20261011-02'","POOL = DIAG / 'transfer-word-layer-flatten-owned-floor-20261011-01'"),
 ("MODULE = 'TransferWordLayeredObjectRead01'","MODULE = 'TransferWordLayerFlatten01'"),
 ('len(current) == 5','len(current) == 8'),
 ('len(records) == 123 and len(audits) == 1051','len(records) == 124 and len(audits) == 1059'),
 ("'objects': 123","'objects': 124"),
 ('len(names) == 8','len(names) == 4'),
 ("'imports': ['ShielddSecurity.TransferPendingSaturatingCapacity01']","'imports': ['ShielddSecurity.TransferWordLayeredObjectRead01']"),
 ("'fresh_audits': 8, 'inherited_audits': 1051","'fresh_audits': 4, 'inherited_audits': 1059"),
 ('LAYERED_WORD_GETTER_COMPLETE_ONE_HUNDRED_TWENTY_THREE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','WORD_LAYER_FLATTEN_COMPLETE_ONE_HUNDRED_TWENTY_FOUR_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')]:replace(a,b)
start=s.index('stdout = UPSTREAM / ');end=s.index('assert len(records)',start)
s=s[:start]+s[start:end].replace('TransferPendingSaturatingCapacity01','TransferWordLayeredObjectRead01')+s[end:]
s=s.replace('one-hundred-twenty-three-module','one-hundred-twenty-four-module').replace('1051 inherited full reports','1059 inherited full reports')
scope=('Symbolic newest-first checked typed object lookup composes exactly with older stack and reverse traversal equals original oldest-first StateDelta applyLayers object observation. Live checked source stack equals functional layer application and exact flatten(empty,layers) object observation, without selected object/getter-success/coherence premise. Four complete theorem audits; no new definitions. Constructed Some layers specify live branch; wrong type can still panic and all native liveness/locks/Clone/Any/persistent map/ownership/concurrency/compiler bindings remain separate. No ancestor replay/native/control/certification credit; full Transfer OPEN.')
start=s.index('\nmapping = ');end=s.index("\nmapping['saturating_capacity_source_shape']",start)
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()), 'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index('\n',start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'live_layer_functional_flatten_join':True,'reports':4,'guards_unchanged':True})
