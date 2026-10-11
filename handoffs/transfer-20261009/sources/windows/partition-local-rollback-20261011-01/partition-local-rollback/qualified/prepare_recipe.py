"""Prepare typed indexed rollback and derived captured-root recovery reuse."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-byte-key-cache-20261011-04/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-scalar-reversed-byte-order-20261011-03'", "UPSTREAM = DIAG / 'transfer-byte-key-cache-20261011-04'")
replace("POOL = DIAG / 'transfer-byte-key-cache-owned-floor-20261011-04'", "POOL = DIAG / 'transfer-partition-local-rollback-owned-floor-20261011-01'")
replace("MODULE = 'TransferByteKeyCache01'", "MODULE = 'TransferPartitionLocalRollback01'")
replace("stdout = UPSTREAM / 'runs/01-TransferScalarReversedByteOrder01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferByteKeyCache01/stdout.txt'")
replace('assert len(current) == 8','assert len(current) == 7')
replace("records.append(('TransferScalarReversedByteOrder01'", "records.append(('TransferByteKeyCache01'")
replace("    'handwritten/TransferScalarReversedByteOrder01.lean', 'project/ShielddSecurity/TransferScalarReversedByteOrder01.lean']]", "    'handwritten/TransferByteKeyCache01.lean', 'project/ShielddSecurity/TransferByteKeyCache01.lean']]")
replace('assert len(records) == 105 and len(audits) == 936','assert len(records) == 106 and len(audits) == 943')
replace("'objects': 105", "'objects': 106")
s=s.replace('one-hundred-five-module','one-hundred-six-module').replace('936 inherited','943 inherited')
replace("'imports': ['ShielddSecurity.TransferScalarReversedByteOrder01']", "'imports': ['ShielddSecurity.TransferByteKeyCache01']")
replace('assert len(names) == 7','assert len(names) == 4');replace("'fresh_audits': 7", "'fresh_audits': 4")
replace("[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', runner")
start=s.index('\nmapping = ');end=s.index("\nmapping['corrected_finalization_source_order']",start)
scope='Partition-local typed rollback changes only selected root and preserves all other roots even on error, while own updated root and possible error remain independent observations. Derived forward-partition frame instantiates original captured/current recurrence and complete recovery equivalence without caller frame premise. Four reports one definition/three theorems; does not assume own-root restoration/success/health/durability. Actual NOMT handle isolation/concurrent observations/locks/compiler/full native trace/ownership/filesystem/crash correspondence remains explicit; zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
a="plan['source_repairs'] = ";start=s.index(a);end=s.index('\n',start);s=s[:start]+a+repr(scope)+s[end:]
s=s.replace('BYTE_KEY_CACHE_COMPLETE_ONE_HUNDRED_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','PARTITION_LOCAL_ROLLBACK_COMPLETE_ONE_HUNDRED_SIX_MODULE_CLOSURE_SELF_REVIEWED_UNRUN').replace("'inherited_audits': 936", "'inherited_audits': 943")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':4,'inherited_reports':943,'owned_modules':106,'native_partition_binding_open':True})
