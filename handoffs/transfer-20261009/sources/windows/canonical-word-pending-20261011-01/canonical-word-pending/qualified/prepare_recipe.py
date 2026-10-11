"""Instantiate reusable symbolic map proof instead of rewriting concrete field terms."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
(ROOT/'handwritten').mkdir()
source=(DIAG/'transfer-canonical-word-pending-20261011-02/handwritten/TransferCanonicalWordPending01.lean').read_text()
source=source.replace('import ShielddSecurity.TransferScalarCanonicalKey01','import ShielddSecurity.TransferSymbolicFieldMap01')
start=source.index('  rw [List.map_map]\n',source.index('theorem canonical_key_list_roundtrips'))
end=source.index('\ntheorem supported_finite_pending_enum_roundtrips',start)
source=source[:start]+'''  exact TransferSymbolicFieldMap01.finite_field_list_roundtrip_follows_from_symbolic_pointwise_inverse
    encodeWordScalar (fun scalar => scalarKey scalar.words) keys
    (fun key inside => (constructed_word_scalar_projects_to_source_key_modulo_field key).trans
      (Nat.mod_eq_of_lt (canonical key inside)))
'''+source[end:]
(ROOT/'handwritten/TransferCanonicalWordPending01.lean').write_text(source)
s=(DIAG/'transfer-symbolic-field-map-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
("UPSTREAM = DIAG / 'transfer-scalar-canonical-key-20261011-03'","UPSTREAM = DIAG / 'transfer-symbolic-field-map-20261011-01'"),
("POOL = DIAG / 'transfer-symbolic-field-map-owned-floor-20261011-01'","POOL = DIAG / 'transfer-canonical-word-pending-owned-floor-20261011-03'"),
("MODULE = 'TransferSymbolicFieldMap01'","MODULE = 'TransferCanonicalWordPending01'"),
("stdout = UPSTREAM / 'runs/01-TransferScalarCanonicalKey01/stdout.txt'","stdout = UPSTREAM / 'runs/01-TransferSymbolicFieldMap01/stdout.txt'"),
('assert len(current) == 8','assert len(current) == 2'),
("records.append(('TransferScalarCanonicalKey01'","records.append(('TransferSymbolicFieldMap01'"),
("    'handwritten/TransferScalarCanonicalKey01.lean', 'project/ShielddSecurity/TransferScalarCanonicalKey01.lean']]","    'handwritten/TransferSymbolicFieldMap01.lean', 'project/ShielddSecurity/TransferSymbolicFieldMap01.lean']]"),
('assert len(records) == 116 and len(audits) == 1013','assert len(records) == 117 and len(audits) == 1015'),
("'objects': 116","'objects': 117"),
("'imports': ['ShielddSecurity.TransferScalarCanonicalKey01']","'imports': ['ShielddSecurity.TransferSymbolicFieldMap01']"),
('assert len(names) == 2','assert len(names) == 8'),
("'fresh_audits': 2","'fresh_audits': 8")]:replace(a,b)
s=s.replace('one-hundred-sixteen-module','one-hundred-seventeen-module').replace('1013 inherited','1015 inherited')
start=s.index('\nmapping = ');end=s.index("\nmapping['corrected_finalization_source_order']",start)
scope='Concrete finite pending enum fields are canonical typed raw Scalar vectors constructed through actual modeled LE/parser/choice/R2 decoder. Source key projection gives key mod p for arbitrary Nat; supported canonical finite enum/list fields derive exact roundtrip and coherent bounded current Pending restoration. Eight reports three definitions/one inductive/four theorems; no arbitrary field inverse/roundtrip premise. Symbolic map theorem instantiation avoids concrete field normalization after two complete kernel-memory failures, retained with zero credit. Seen set remains extensional finite member list; native private Scalar/imbl containers/Clone/Any/primitive/compiler/Choice/CtOption/full trace bindings remain explicit. Unsupported Nat keys wrap and receive no exact roundtrip claim; zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}\nmapping['scalar_decode_source_shape']=pin(DIAG/'transfer-scalar-byte-decode-20261011-02/context/decoder-shape.json')\nmapping['wide_product_source_shape']=pin(DIAG/'transfer-scalar-wide-product-20261011-01/context/wide-product-shape.json')\nmapping['wide_reduction_source_shape']=pin(DIAG/'transfer-scalar-wide-round-20261011-04/context/wide-reduction-shape.json')\nmapping['r2_decoder_payload_source_shape']=pin(DIAG/'transfer-scalar-r2-payload-20261011-01/context/r2-decoder-payload-shape.json')"+s[end:]
a="plan['source_repairs'] = ";start=s.index(a);end=s.index('\n',start);s=s[:start]+a+repr(scope)+s[end:]
s=s.replace('SYMBOLIC_FIELD_MAP_COMPLETE_ONE_HUNDRED_SIXTEEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','CANONICAL_WORD_PENDING_COMPLETE_ONE_HUNDRED_SEVENTEEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN').replace("'inherited_audits': 1013","'inherited_audits': 1015")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':8,'inherited_reports':1015,'owned_modules':117,'native_credit':0,'guards_unchanged':True})
