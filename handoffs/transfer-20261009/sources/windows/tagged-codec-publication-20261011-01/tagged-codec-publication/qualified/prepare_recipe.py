"""Construct a heterogeneous typed object codec and prove its model roundtrip."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
oldSource=(DIAG/'transfer-native-getter-publication-20261011-01/handwritten/TransferNativeGetterPublication01.lean').read_text()
source=oldSource[:oldSource.index('/-!')]
source=source.replace('import ShielddSecurity.TransferFixedFinalizerPublication01','import ShielddSecurity.TransferNativeGetterPublication01').replace('namespace ShielddSecurity.TransferNativeGetterPublication01','namespace ShielddSecurity.TransferTaggedCodecPublication01')
source+='''open TransferNativeGetterPublication01 (installGetterIo)
/-! Heterogeneous typed source-model objects distinguish native pending enum
from every other native object. Encoding injects the enum tag; decoding that
tag recovers the exact enum, and other tags restore the default empty enum.
Native cached tree uses the other-object tag. Model roundtrip is proved with
no caller codec hypothesis; native Any/downcast/Clone/finite enum/field/cache
and full trace correspondence remain explicit. Ghost-extended carrier still
exists in the old source closure; no global ghost erasure/native credit. -/

def TaggedObject (Other : Type) : Type := NativePending ⊕ Other

def encodePending {Other : Type} (native : NativePending) : TaggedObject Other := .inl native

def decodePending {Other : Type} : TaggedObject Other → NativePending
  | .inl native => native
  | .inr _ => .opened [] []

structure OtherFinalizationWrites (Other E A : Type) where
  nativeTreeObject : Other
  verifiable : Writes Bytes
  nonverifiable : Writes Bytes
  events : List E
  queued : List A

def liftWrites {Other E A : Type} (writes : OtherFinalizationWrites Other E A) : FinalizationWrites (TaggedObject Other) E A :=
  ⟨.inr writes.nativeTreeObject, writes.verifiable, writes.nonverifiable, writes.events, writes.queued⟩

def installTaggedIo {Other E A : Type}
    (writesOf : Fin (2 ^ 64) → State (ExtendedObject (TaggedObject Other)) → List A → OtherFinalizationWrites Other E A)
    (baseIo : TransferEndToEnd01.Io (ExtendedObject (TaggedObject Other)) E A) : TransferEndToEnd01.Io (ExtendedObject (TaggedObject Other)) E A :=
  installGetterIo encodePending decodePending (fun height state queued => liftWrites (writesOf height state queued)) baseIo

theorem tagged_pending_restore_roundtrip {Other : Type} (native : NativePending) :
    restore (decodePending (encodePending (Other := Other) native)) = restore native := rfl

'''
start=oldSource.index('theorem native_getter_source_finalization_publishes_exact_global_mathematical_input_vector');end=oldSource.index('\nset_option pp.all true in',start)
t=oldSource[start:end]
t=t.replace('native_getter_source_finalization_publishes_exact_global_mathematical_input_vector','tagged_codec_source_finalization_publishes_exact_global_mathematical_input_vector',1)
t=t.replace('{O E K X Tree A I : Type}','{Other E K X Tree A I : Type}',1)
start=t.index('    (encodeNative : ');end=t.index('    (inputs : ',start);t=t[:start]+t[end:]
t=t.replace('FinalizationWrites O E A','OtherFinalizationWrites Other E A')
start=t.index(' := by\n');t=t[:start]+''' := by
  exact TransferNativeGetterPublication01.native_getter_source_finalization_publishes_exact_global_mathematical_input_vector
    (encodePending (Other := Other)) (decodePending (Other := Other))
    (fun native _ => tagged_pending_restore_roundtrip native)
    inputs wordOf sourceRequests parent queued final storedNativeDefault walkedNative
    (fun height state queued => liftWrites (writesOf height state queued)) baseIo host height root currentState success
'''
head,proof=t.split(' := by\n',1)
head=head.replace('installGetterIo encodeNative decodeNative writesOf baseIo','installTaggedIo writesOf baseIo')
head=re.sub(r'\bO\b','(TaggedObject Other)',head).replace('encodeNative','encodePending').replace('decodeNative','decodePending')
source+=head+' := by\n'+proof
names=re.findall(r'^(?:structure|def|theorem) ([A-Za-z0-9_]+)',source,re.M);assert len(names)==8
for name in names:source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferTaggedCodecPublication01\n'
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferTaggedCodecPublication01.lean').write_text(source)
s=(DIAG/'transfer-native-getter-publication-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-fixed-finalizer-publication-20261011-01'", "UPSTREAM = DIAG / 'transfer-native-getter-publication-20261011-01'")
replace("POOL = DIAG / 'transfer-native-getter-publication-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-tagged-codec-publication-owned-floor-20261011-01'")
replace("MODULE = 'TransferNativeGetterPublication01'", "MODULE = 'TransferTaggedCodecPublication01'")
replace("stdout = UPSTREAM / 'runs/01-TransferFixedFinalizerPublication01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferNativeGetterPublication01/stdout.txt'")
replace('assert len(current) == 8','assert len(current) == 3')
replace("records.append(('TransferFixedFinalizerPublication01'", "records.append(('TransferNativeGetterPublication01'")
replace("    'handwritten/TransferFixedFinalizerPublication01.lean', 'project/ShielddSecurity/TransferFixedFinalizerPublication01.lean']]", "    'handwritten/TransferNativeGetterPublication01.lean', 'project/ShielddSecurity/TransferNativeGetterPublication01.lean']]")
replace('assert len(records) == 97 and len(audits) == 894','assert len(records) == 98 and len(audits) == 897')
replace("'objects': 97", "'objects': 98")
s=s.replace('ninety-seven-module','ninety-eight-module').replace('894 inherited','897 inherited')
replace("'imports': ['ShielddSecurity.TransferFixedFinalizerPublication01']", "'imports': ['ShielddSecurity.TransferNativeGetterPublication01']")
replace('assert len(names) == 3','assert len(names) == 8');replace("'fresh_audits': 3", "'fresh_audits': 8")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Concrete heterogeneous source-model native object sum distinguishes pending enum from every other native object; enum-tag encode/decode exact restore roundtrip is kernel rfl, cached tree uses other-object tag. Installed codec/getter/fixed six source mutations/proved key labels/typed input requests yield exact global mathematical vector/native sealed object/accepted inputs/application root/Ready writer/Idle Host/physical recovered boundary from ordinary success. Eight complete reports: five definitions/one structure/two theorems. No caller codec roundtrip/reached getter/source projection/final field frame/key injection supplied. Native Any/downcast/Clone/enum/field/cache/selector/full trace/ownership/OS binding remains explicit. Old extended ghost carrier persists; no global ghost erasure/native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
s=s.replace('NATIVE_GETTER_PUBLICATION_COMPLETE_NINETY_SEVEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','TAGGED_CODEC_PUBLICATION_COMPLETE_NINETY_EIGHT_MODULE_CLOSURE_SELF_REVIEWED_UNRUN').replace("'inherited_audits': 894", "'inherited_audits': 897")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':8,'inherited_reports':897,'owned_modules':98,'full_native_trace_still_open':True})
