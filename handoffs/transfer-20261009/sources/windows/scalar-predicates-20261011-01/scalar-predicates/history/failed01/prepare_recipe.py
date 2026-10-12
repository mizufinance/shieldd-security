from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-scalar-extended-semantics-20261012-01/prepare.py').read_text()
for a,b in [
 ("UP=DIAG/'transfer-scalar-input-semantics-20261012-04'","UP=DIAG/'transfer-scalar-extended-semantics-20261012-01'"),
 ("POOL=DIAG/'transfer-scalar-extended-semantics-owned-floor-20261012-01'","POOL=DIAG/'transfer-scalar-predicates-owned-floor-20261012-01'"),
 ("MODULE='TransferScalarExtendedSemantics01'","MODULE='TransferScalarPredicates01'"),
 ('runs/01-TransferScalarInputSemantics01/stdout.txt','runs/01-TransferScalarExtendedSemantics01/stdout.txt'),
 ("records.append(('TransferScalarInputSemantics01'","records.append(('TransferScalarExtendedSemantics01'"),
 ('len(records)==213 and len(audits)==1520','len(records)==214 and len(audits)==1527'),
 ('handwritten/TransferScalarInputSemantics01.lean','handwritten/TransferScalarExtendedSemantics01.lean'),
 ('project/ShielddSecurity/TransferScalarInputSemantics01.lean','project/ShielddSecurity/TransferScalarExtendedSemantics01.lean'),
 ("'objects':213","'objects':214"),
 ('qualified213-module1520-report','qualified214-module1527-report'),
 ('len(names)==7','len(names)==13'),
 ('scalar-extended-semantics-shape.json','scalar-predicates-shape.json'),
 ('scalar_extended_semantics_source_shape','scalar_predicates_source_shape'),
 ("'imports':['ShielddSecurity.TransferScalarInputSemantics01','ShielddSecurity.TransferScalarPowField01','ShielddSecurity.TransferScalarInvertField01']","'imports':['ShielddSecurity.TransferScalarExtendedSemantics01','ShielddSecurity.TransferScalarConstantEquality01']"),
 ('exact213-module qualified','exact214-module qualified'),
 ("'fresh_audits':7","'fresh_audits':13"),
 ('SCALAR_EXTENDED_SEMANTICS_SELF_REVIEWED_UNRUN','SCALAR_PREDICATES_SELF_REVIEWED_UNRUN')]:
 expected=2 if a=='scalar_extended_semantics_source_shape' else 1
 assert s.count(a)==expected,(a,s.count(a),expected);s=s.replace(a,b)
start=s.index("scope='");end=s.index('\n',start)
scope='Thirteen complete source-model declarations derive Scalar equality/zero/parity predicates and locked Choice-to-bool value conversion. Canonical words derive exact mathematical equality and zero. Exact first typed LE byte low-bit gives mathematical field parity, and both source equality/parity producers derive their byte0/1 contracts. General bool conversion uses the documented valid-byte premise explicitly; no validity inferred from Rust type. Fixed32-byte source serialization prevents index0 absence. Compiler/volatile/native indexing/ABI/private caller origins/timing/full Transfer remain open.'
s=s[:start]+"scope="+repr(scope)+s[end:]
extra="""assert 'source.0 != 0' in raw and 'debug_assert!((source.0 == 0u8) | (source.0 == 1u8));' in raw
scalar_raw=Path(subtle_context['scalar_source']['path']).read_text()
assert 'Choice::from(self.to_bytes()[0] & 1)' in scalar_raw and 'self.0 == Self::zero().0' in scalar_raw
"""
at=s.index("plan['artifact_policy']");s=s[:at]+extra+s[at:]
(ROOT/'prepare.py').write_bytes(s.encode())
print({'fresh13_declarations','source_predicate_and_choice_bodies_checked','exact214_module1527_report_extended_semantics_predecessor','all_guards_unchanged','no_ancestor_replay'})
