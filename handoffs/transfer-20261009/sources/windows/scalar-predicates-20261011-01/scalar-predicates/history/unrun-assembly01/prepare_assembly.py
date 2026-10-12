from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-extended-semantics-endpoint-20261012-01/assemble.py').read_text()
for a,b in [
 ("CURRENT=DIAG/'transfer-scalar-extended-semantics-20261012-01'","CURRENT=DIAG/'transfer-scalar-predicates-20261012-01'"),
 ("CHECKPOINT=DIAG/'transfer-scalar-extended-semantics-checkpoint-20261012-01'","CHECKPOINT=DIAG/'transfer-scalar-predicates-checkpoint-20261012-01'"),
 ("MODULE='TransferScalarExtendedSemantics01'","MODULE='TransferScalarPredicates01'"),
 ("PARENT=DIAG/'transfer-scalar-input-semantics-endpoint-20261012-03'","PARENT=DIAG/'transfer-scalar-extended-semantics-endpoint-20261012-01'"),
 ("archive=ROOT/'portable-windows-scalar-extended-semantics-endpoint01.tar.xz'","archive=ROOT/'portable-windows-scalar-predicates-endpoint01.tar.xz'"),
 ("parent_archive=PARENT/'portable-windows-scalar-input-semantics-endpoint01.tar.xz'","parent_archive=PARENT/'portable-windows-scalar-extended-semantics-endpoint01.tar.xz'"),
 ('30b878090316f13c75af4643e298052137f4680843d231f4d5864fa69946a343','de6fa13fad4d404a735050aa43c6e2a8594c6737458c32886ae162fdde895e74'),
 ('len(fresh)==7','len(fresh)==13'),
 ("len(kinds)==7 and kinds.count('def')==2 and kinds.count('theorem')==5","len(kinds)==13 and kinds.count('def')==5 and kinds.count('theorem')==8"),
 ("pool['objects']==213 and len(pool['inherited_public_reports'])==1520","pool['objects']==214 and len(pool['inherited_public_reports'])==1527"),
 ("'module':'TransferScalarInputSemantics01'","'module':'TransferScalarExtendedSemantics01'"),
 ("len(parent_selected)==213 and len(pool['selected'])==213","len(parent_selected)==214 and len(pool['selected'])==214"),
 ("'complete_owned_modules':213,'inherited_complete_reports':1520","'complete_owned_modules':214,'inherited_complete_reports':1527"),
 ('original213-module1520-report','original214-module1527-report'),
 ('handwritten complete independent constant/u64/random/square/power/inverse/selection semantics and structural source evaluator induction','handwritten complete source scalar/Choice equality, zero and parity predicate semantics'),
 ("add(stdout,'reports/fresh-7-complete-declarations.txt'","add(stdout,'reports/fresh-13-complete-declarations.txt'"),
 ('qualified213-module first import root and1520','qualified214-module first import root and1527'),
 ('scalar-extended-semantics-shape.json','scalar-predicates-shape.json'),
 ('SOURCE_SCALAR_EXTENDED_EVALUATOR_INDEPENDENT_FIELD_AND_REFUSAL_SEMANTICS_QUALIFIED','SOURCE_SCALAR_EQUALITY_ZERO_PARITY_AND_CHOICE_BOOLEAN_PREDICATES_QUALIFIED'),
 ("'fresh_definition_audits':2","'fresh_definition_audits':5"),
 ("'fresh_theorem_audits':5","'fresh_theorem_audits':8"),
 ("'fresh_complete_public_audits':7","'fresh_complete_public_audits':13"),
 ("'inherited_complete_public_audits':1520","'inherited_complete_public_audits':1527"),
 ('transfer-scalar-extended-semantics-endpoint-v1','transfer-scalar-predicates-endpoint-v1'),
 ("'fresh_audits':7,'inherited_audits':1520","'fresh_audits':13,'inherited_audits':1527")]:
 expected=3 if a=='scalar-extended-semantics-shape.json' else 2 if a=="'fresh_audits':7,'inherited_audits':1520" else 1
 assert s.count(a)==expected,(a,s.count(a),expected);s=s.replace(a,b)
(ROOT/'assemble.py').write_bytes(s.encode())
print({'fresh13_declarations','exact_library_predicate_sources_retained','complete214_module1527_report_extended_semantics_predecessor','no_ancestor_replay'})
