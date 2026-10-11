"""Prepare bounded all-return primitive/raw equality against native-only encoding."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-native-raw-pending-20261011-03/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-native-pending-write-20261011-01'", "UPSTREAM = DIAG / 'transfer-native-raw-pending-20261011-03'")
replace("POOL = DIAG / 'transfer-native-raw-pending-owned-floor-20261011-03'", "POOL = DIAG / 'transfer-native-ghost-erasure-owned-floor-20261011-01'")
replace("MODULE = 'TransferNativeRawPending01'", "MODULE = 'TransferNativeGhostErasure01'")
s=s.replace("'runs/01-TransferNativePendingWrite01/stdout.txt'", "'runs/01-TransferNativeRawPending01/stdout.txt'",1)
replace("records.append(('TransferNativePendingWrite01'", "records.append(('TransferNativeRawPending01'")
replace("    'handwritten/TransferNativePendingWrite01.lean', 'project/ShielddSecurity/TransferNativePendingWrite01.lean']]", "    'handwritten/TransferNativeRawPending01.lean', 'project/ShielddSecurity/TransferNativeRawPending01.lean']]")
replace('assert len(records) == 73 and len(audits) == 721', 'assert len(records) == 74 and len(audits) == 724')
replace("'objects': 73", "'objects': 74")
s=s.replace('seventy-three-module','seventy-four-module').replace('721 inherited','724 inherited')
replace("'imports': ['ShielddSecurity.TransferNativePendingWrite01']", "'imports': ['ShielddSecurity.TransferNativeRawPending01']")
replace('assert len(names) == 3','assert len(names) == 5')
replace("'fresh_audits': 3", "'fresh_audits': 5")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Exact functional source-model equality of accepted ghost-extended finite encoder and native-only sum-branch encoder for every returned nullifier primitive outcome under actual previous invariant/canonical bounds, actual input canonical bounds and native word guard. Successful inspection derives supported arguments before encode; rejected/empty/no-source paths do not encode. Same actual note and volume callbacks/observations reused: symbolic notes equality, raw reshape equality and full raw transfer equality including all returned errors/capability branches. One definition/four complete proofs. Native-only comparison does not assert encodability of unsupported arguments; these are never evaluated at successful primitive writes. This is model erasure only, not actual Rust trace, native codec/getter/field-byte/finite library/input/callback/ownership/OS closure. Zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh actual bounded primitive/raw all-return equality, erasing unsupported source-model ghost encodings while reusing identical actual callbacks. Qualified fixed-codec raw source03 reused3 plus complete 724-report/74-module closure without replay. Historical failures fully retained, physical and per-run guards unchanged.'"+s[end:]
s=s.replace('SOURCE_FIXED_CODEC_CANONICAL_NATIVE_PENDING_ANY_RETURN_RAW_RESHAPE','SOURCE_BOUNDED_NATIVE_PENDING_GHOST_ERASURE_ALL_RETURN_PRIMITIVE_AND_RAW')
s=s.replace('NATIVE_RAW_PENDING_COMPLETE_SEVENTY_THREE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','NATIVE_GHOST_ERASURE_COMPLETE_SEVENTY_FOUR_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'inherited_audits': 721", "'inherited_audits': 724")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':5,'inherited_reports':724,'owned_modules':74})
