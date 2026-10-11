"""Source-order correction in fresh model; keep old qualified evidence immutable."""
from pathlib import Path
import json,re
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
old=(DIAG/'transfer-fixed-finalizer-publication-20261011-01/handwritten/TransferFixedFinalizerPublication01.lean').read_text()
source=old[:old.index('set_option pp.all true in')]
source=source.replace('import ShielddSecurity.TransferInjectiveKeyPublication01','import ShielddSecurity.TransferCanonicalWordEquality01').replace('namespace ShielddSecurity.TransferFixedFinalizerPublication01','namespace ShielddSecurity.TransferSourceOrderedFinalizer01')
start=source.index('structure FinalizationWrites');end=source.index('def fixedMutations',start)
source=source[:start]+'open TransferFixedFinalizerPublication01 (FinalizationWrites)\n\n'+source[end:]
start=source.index('  [⟨');end=source.index('\n\ndef toEffects',start)
oldlist=source[start:end]
entries=re.findall(r'⟨\[.*?\], by decide, (?:none|some \(\.inl nativeTreeObject\))⟩',oldlist)
assert len(entries)==6
order=[0,1,3,4,5,2];ordered=[entries[i] for i in order]
source=source[:start]+'  ['+',\n   '.join(ordered)+']'+source[end:]
start=source.index('theorem fixed_mutation_recipe_has_exact_source_key_order');end=source.index('\n\ntheorem fixed_mutation_recipe_has_six_operations',start)
keys=[json.loads(e[1:e.index('], by decide')+1]) for e in ordered]
association=json.loads((DIAG/'transfer-fixed-finalizer-publication-20261011-01/context/fixed-finalization-call-shape.json').read_text())
assert keys==[association['known_mutation_order'][i]['utf8'] for i in order]
assert association['call_positions']==sorted(association['call_positions']) and len(association['call_positions'])==5
association['known_mutation_order']=[association['known_mutation_order'][i] for i in order]
association['scope']+=' Fresh table follows authenticated call positions; original inventory order was not call order. Static association only.'
(ROOT/'context').mkdir();(ROOT/'context/corrected-finalization-call-order.json').write_text(json.dumps(association,indent=2,sort_keys=True)+'\n')
source=source[:start]+'''theorem fixed_mutation_recipe_has_exact_source_key_order {O : Type} (tree : O) :
    (fixedMutations tree).map (fun mutation => mutation.key) = '''+repr(keys)+''' := rfl'''+source[end:]
source=source.replace('proof supplied. Source call ordering association is static, not an exhaustive','proof supplied. Fresh recipe corrects the inherited model order to the\npinned SCT then compliance then routing source call order. The inherited\nlist stays qualified only as its defined model. Association is static, not an exhaustive')
names=re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',source,re.M);assert len(names)==7
for name in names:source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferSourceOrderedFinalizer01\n'
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferSourceOrderedFinalizer01.lean').write_text(source)
s=(DIAG/'transfer-canonical-word-equality-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-complete-block-driver-20261011-02'", "UPSTREAM = DIAG / 'transfer-canonical-word-equality-20261011-02'")
replace("POOL = DIAG / 'transfer-canonical-word-equality-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-source-ordered-finalizer-owned-floor-20261011-02'")
replace("MODULE = 'TransferCanonicalWordEquality01'", "MODULE = 'TransferSourceOrderedFinalizer01'")
replace("stdout = UPSTREAM / 'runs/01-TransferCompleteBlockDriver01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferCanonicalWordEquality01/stdout.txt'")
replace('assert len(current) == 2','assert len(current) == 6')
replace("records.append(('TransferCompleteBlockDriver01'", "records.append(('TransferCanonicalWordEquality01'")
replace("    'handwritten/TransferCompleteBlockDriver01.lean', 'project/ShielddSecurity/TransferCompleteBlockDriver01.lean']]", "    'handwritten/TransferCanonicalWordEquality01.lean', 'project/ShielddSecurity/TransferCanonicalWordEquality01.lean']]")
replace('assert len(records) == 101 and len(audits) == 911','assert len(records) == 102 and len(audits) == 917')
replace("'objects': 101", "'objects': 102")
s=s.replace('one-hundred-one-module','one-hundred-two-module').replace('911 inherited','917 inherited')
replace("'imports': ['ShielddSecurity.TransferCompleteBlockDriver01']", "'imports': ['ShielddSecurity.TransferCanonicalWordEquality01']")
replace('assert len(names) == 6','assert len(names) == 7');replace("'fresh_audits': 6", "'fresh_audits': 7")
replace("[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', runner")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Fresh source-ordered known finalizer fixes inherited fixed-list sequence: materialization deletion, cached tree put, user registrations/statuses/assets deletion, routing deletion. Exact symbolic literals are checked against authenticated source call-order association. Three definitions/four theorems derive full typed source model publication with corrected order. Inherited old finalizer theorems remain their defined model only; this module does not assert full native call trace completeness, hidden callee purity, values, cache, ownership or OS correspondence. Zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
s=s.replace('CANONICAL_WORD_EQUALITY_COMPLETE_ONE_HUNDRED_ONE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SOURCE_ORDERED_FINALIZER_COMPLETE_ONE_HUNDRED_TWO_MODULE_CLOSURE_SELF_REVIEWED_UNRUN').replace("'inherited_audits': 911", "'inherited_audits': 917")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':7,'inherited_reports':917,'owned_modules':102,'static_known_order_checked':True})
