"""Prove an injective natural label for arbitrary byte lists and install it in publication."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
oldSource=(DIAG/'transfer-installed-source-publication-20261011-02/handwritten/TransferInstalledSourcePublication01.lean').read_text()
source=oldSource[:oldSource.index('/-!')]
source=source.replace('import ShielddSecurity.TransferKnownFinalizerPublication01','import ShielddSecurity.TransferInstalledSourcePublication01').replace('namespace ShielddSecurity.TransferInstalledSourcePublication01','namespace ShielddSecurity.TransferInjectiveKeyPublication01')
source+='''open TransferInstalledSourcePublication01 (SourceRequest installRequests)
/-! Pure injective natural labels for arbitrary finite Nat byte lists. This
is a symbolic key renaming, not hashing or a native cache implementation.
Empty/odd-head/even-successor coding derives global injection with finite
induction and small arithmetic lemmas. Installed whole source publication
uses the proved injection, with no caller key-injectivity premise. Native
String/byte/cache key identity and full trace/selector/codec/ownership/OS
correspondence remain explicit; no native/control/certification credit. -/

def consCode : Nat → Nat → Nat
  | 0, tail => 2 * tail + 1
  | head + 1, tail => 2 * (consCode head tail + 1)

def keyCode : Bytes → Nat
  | [] => 0
  | head :: tail => consCode head (keyCode tail)

theorem consCode_is_positive (head tail : Nat) : 0 < consCode head tail := by
  cases head <;> simp only [consCode] <;> omega

theorem consCode_derives_exact_head_and_tail (a b x y : Nat) (same : consCode a x = consCode b y) :
    a = b ∧ x = y := by
  induction a generalizing b x y with
  | zero =>
    cases b with
    | zero =>
      change 2 * x + 1 = 2 * y + 1 at same
      exact ⟨rfl, by omega⟩
    | succ b =>
      change 2 * x + 1 = 2 * (consCode b y + 1) at same
      omega
  | succ a ih =>
    cases b with
    | zero =>
      change 2 * (consCode a x + 1) = 2 * y + 1 at same
      omega
    | succ b =>
      have inner : consCode a x = consCode b y := by
        change 2 * (consCode a x + 1) = 2 * (consCode b y + 1) at same
        omega
      obtain ⟨heads, tails⟩ := ih b x y inner
      exact ⟨congrArg Nat.succ heads, tails⟩

theorem keyCode_is_injective : Function.Injective keyCode := by
  intro left
  induction left with
  | nil =>
    intro right same
    cases right with
    | nil => rfl
    | cons head tail =>
      have positive := consCode_is_positive head (keyCode tail)
      change 0 = consCode head (keyCode tail) at same
      omega
  | cons head tail ih =>
    intro right same
    cases right with
    | nil =>
      have positive := consCode_is_positive head (keyCode tail)
      change consCode head (keyCode tail) = 0 at same
      omega
    | cons other rest =>
      have pair := consCode_derives_exact_head_and_tail head other (keyCode tail) (keyCode rest) same
      exact (congrArg (fun h : Nat => h :: tail) pair.1).trans (congrArg (List.cons other) (@ih rest pair.2))

'''
start=oldSource.index('theorem installed_source_and_finalizer_publish_exact_global_mathematical_input_vector');end=oldSource.index('\nset_option pp.all true in',start)
t=oldSource[start:end]
t=t.replace('installed_source_and_finalizer_publish_exact_global_mathematical_input_vector','injective_labeled_source_and_finalizer_publish_exact_global_mathematical_input_vector',1)
a='    (project : Bytes → Nat) (injection : Function.Injective project)\n'
assert t.count(a)==1
t=t.replace(a,'')
start=t.index(' := by\n');t=t[:start]+''' := by
  exact TransferInstalledSourcePublication01.installed_source_and_finalizer_publish_exact_global_mathematical_input_vector
    encodeNative decodeNative supportedRoundtrip keyCode keyCode_is_injective inputs wordOf sourceRequests parent queued final storedNativeDefault
    walkedNative effectsOf baseIo host height root currentState typedGetter success
'''
head,proof=t.split(' := by\n',1)
head=re.sub(r'\bproject\b','keyCode',head)
source+=head+' := by\n'+proof
names=re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',source,re.M)
assert len(names)==6
for name in names: source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferInjectiveKeyPublication01\n'
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferInjectiveKeyPublication01.lean').write_text(source)
s=(DIAG/'transfer-installed-source-publication-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-known-finalizer-publication-20261011-03'", "UPSTREAM = DIAG / 'transfer-installed-source-publication-20261011-02'")
replace("POOL = DIAG / 'transfer-installed-source-publication-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-injective-key-publication-owned-floor-20261011-02'")
replace("MODULE = 'TransferInstalledSourcePublication01'", "MODULE = 'TransferInjectiveKeyPublication01'")
replace("stdout = UPSTREAM / 'runs/01-TransferKnownFinalizerPublication01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferInstalledSourcePublication01/stdout.txt'")
replace("records.append(('TransferKnownFinalizerPublication01'", "records.append(('TransferInstalledSourcePublication01'")
replace("    'handwritten/TransferKnownFinalizerPublication01.lean', 'project/ShielddSecurity/TransferKnownFinalizerPublication01.lean']]", "    'handwritten/TransferInstalledSourcePublication01.lean', 'project/ShielddSecurity/TransferInstalledSourcePublication01.lean']]")
replace('assert len(records) == 94 and len(audits) == 873','assert len(records) == 95 and len(audits) == 880')
replace("'objects': 94", "'objects': 95")
s=s.replace('ninety-four-module','ninety-five-module').replace('873 inherited','880 inherited')
replace("'imports': ['ShielddSecurity.TransferKnownFinalizerPublication01']", "'imports': ['ShielddSecurity.TransferInstalledSourcePublication01']")
replace('assert len(names) == 7','assert len(names) == 6')
replace("'fresh_audits': 7", "'fresh_audits': 6")
replace("[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', runner")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Pure recursive natural key label is injective for every finite Nat byte list by symbolic head/tail induction and linear parity/cancellation lemmas. Concrete source request and six-key finalizer publication instantiate proved injection; exact ordered mathematical nullifiers/native sealed object/accepted inputs/application root/Ready writer/Idle Host/physical recovered boundary derive from ordinary success. Six complete reports: two definitions/four theorems. No key-injectivity/source-key equality/canonical bounds/finalization field frame premise supplied. This is symbolic key renaming, not runtime hashing; native String/byte/cache identity/selectors/codec/full trace/ownership/OS bindings remain explicit. Zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
s=s.replace('INSTALLED_SOURCE_PUBLICATION_COMPLETE_NINETY_FOUR_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','INJECTIVE_KEY_PUBLICATION_COMPLETE_NINETY_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'inherited_audits': 873", "'inherited_audits': 880")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':6,'inherited_reports':880,'owned_modules':95,'full_native_trace_still_open':True})
