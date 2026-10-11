"""Compose corrected known source order into absent-start returned whole driver."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
driver=(DIAG/'transfer-complete-block-driver-20261011-02/handwritten/TransferCompleteBlockDriver01.lean').read_text()
absent=(DIAG/'transfer-absent-start-publication-20261011-01/handwritten/TransferAbsentStartPublication01.lean').read_text()
source=driver[:driver.index('/-!')]
source=source.replace('import ShielddSecurity.TransferAbsentStartPublication01','import ShielddSecurity.TransferSourceOrderedFinalizer01').replace('namespace ShielddSecurity.TransferCompleteBlockDriver01','namespace ShielddSecurity.TransferSourceOrderedDriver01').replace(' liftWrites installTaggedIo)',' liftWrites)')
source+='''/-! Corrected source-ordered known finalization is composed into concrete
tagged getter, fresh absent parent, source requests and returned whole driver.
The inherited older fixed list remains only its defined model. Full native
trace/callee/value/primitive/field/cache/snapshot/ownership/OS bindings remain
explicit. No native, control or certification credit. -/

def installSourceOrderedTaggedIo {Other E A : Type}
    (writesOf : Fin (2 ^ 64) → State (ExtendedObject (TaggedObject Other)) → List A → OtherFinalizationWrites Other E A)
    (baseIo : TransferEndToEnd01.Io (ExtendedObject (TaggedObject Other)) E A) :
    TransferEndToEnd01.Io (ExtendedObject (TaggedObject Other)) E A :=
  TransferSourceOrderedFinalizer01.installFixedIo encodePending decodePending
    (fun height state queued => liftWrites (writesOf height state queued))
    {baseIo with ending := {baseIo.ending with decodePending := TransferPendingFiniteCodec01.decode (decodeObject decodePending)}}

'''
start=absent.index('theorem fresh_absent_source_finalization_publishes_exact_global_mathematical_input_vector')
source+=absent[start:absent.index('set_option pp.all true in',start)].replace('TransferFixedFinalizerPublication01.toEffects','TransferSourceOrderedFinalizer01.toEffects').replace('installTaggedIo','installSourceOrderedTaggedIo').replace('exact whole_absent_native_default_block_publishes_exact_global_native_sealed_inputs','exact TransferAbsentStartPublication01.whole_absent_native_default_block_publishes_exact_global_native_sealed_inputs')
start=driver.index('def runCompleteBlock')
source+=driver[start:driver.index('set_option pp.all true in',start)].replace('installTaggedIo','installSourceOrderedTaggedIo').replace('TransferAbsentStartPublication01.fresh_absent_source_finalization_publishes_exact_global_mathematical_input_vector','fresh_absent_source_finalization_publishes_exact_global_mathematical_input_vector')
names=re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',source,re.M);assert len(names)==4
for name in names:source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferSourceOrderedDriver01\n'
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferSourceOrderedDriver01.lean').write_text(source)
s=(DIAG/'transfer-source-ordered-finalizer-20261011-03/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-canonical-word-equality-20261011-02'", "UPSTREAM = DIAG / 'transfer-source-ordered-finalizer-20261011-03'")
replace("POOL = DIAG / 'transfer-source-ordered-finalizer-owned-floor-20261011-03'", "POOL = DIAG / 'transfer-source-ordered-driver-owned-floor-20261011-01'")
replace("MODULE = 'TransferSourceOrderedFinalizer01'", "MODULE = 'TransferSourceOrderedDriver01'")
replace("stdout = UPSTREAM / 'runs/01-TransferCanonicalWordEquality01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferSourceOrderedFinalizer01/stdout.txt'")
replace('assert len(current) == 6','assert len(current) == 7')
replace("records.append(('TransferCanonicalWordEquality01'", "records.append(('TransferSourceOrderedFinalizer01'")
replace("    'handwritten/TransferCanonicalWordEquality01.lean', 'project/ShielddSecurity/TransferCanonicalWordEquality01.lean']]", "    'handwritten/TransferSourceOrderedFinalizer01.lean', 'project/ShielddSecurity/TransferSourceOrderedFinalizer01.lean']]")
replace('assert len(records) == 102 and len(audits) == 917','assert len(records) == 103 and len(audits) == 924')
replace("'objects': 102", "'objects': 103")
s=s.replace('one-hundred-two-module','one-hundred-three-module').replace('917 inherited','924 inherited')
replace("'imports': ['ShielddSecurity.TransferCanonicalWordEquality01']", "'imports': ['ShielddSecurity.TransferSourceOrderedFinalizer01']")
replace('assert len(names) == 7','assert len(names) == 4');replace("'fresh_audits': 7", "'fresh_audits': 4")
replace("[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', runner")
replace("mapping['corrected_finalization_source_order']=pin(ROOT/'context/corrected-finalization-call-order.json')", "mapping['corrected_finalization_source_order']=pin(DIAG/'transfer-source-ordered-finalizer-20261011-03/context/corrected-finalization-call-order.json')")
start=s.index('\nmapping = ');end=s.index("\nmapping['corrected_finalization_source_order']",start)
scope='Corrected SCT/compliance/routing known source order is composed into tagged codec/getter, fresh absent pending parent and complete returned block driver. Four reports: two definitions/two theorems; returned root derives actual successful walk, exact ordered mathematical input vector, native model sealed object, bounded distinct canonical accepted keys, same App/NF boundary and returned Idle/Ready state. No caller walk, current-state, frame, getter, codec or key-injection proofs. Native full trace/callee/value/compiler/field/cache/snapshot/ownership/OS bindings remain explicit; zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
a="plan['source_repairs'] = ";start=s.index(a);end=s.index('\n',start)
s=s[:start]+a+repr(scope)+s[end:]
s=s.replace('SOURCE_ORDERED_FINALIZER_COMPLETE_ONE_HUNDRED_TWO_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SOURCE_ORDERED_DRIVER_COMPLETE_ONE_HUNDRED_THREE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN').replace("'inherited_audits': 917", "'inherited_audits': 924")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':4,'inherited_reports':924,'owned_modules':103,'full_native_binding_open':True})
