from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
prior=DIAG/'transfer-scalar-choice-correspondence-endpoint-20261012-01'
assert not (prior/'manifest.json').exists() and not list(prior.glob('*.tar.xz'))
s=(prior/'assemble.py').read_text()
for old,new in [
 ('SOURCE_PUBLIC_SCALAR_CONSTANTS_EXACT_GENERATOR_ROOT_AND_DELTA_ORDERS_QUALIFIED','SOURCE_WORD_MASK_POWER_AND_EQUALITY_FLAG_INVERSE_COMPOSITION_QUALIFIED'),
 ('transfer-scalar-public-constants-endpoint-v1','transfer-scalar-choice-correspondence-endpoint-v1'),
 ('source-derived canonical raw Scalar-word fields in concrete finite pending enum/list codec','exact typed source word-mask/equality/power/inversion model composition'),
 ('complete two-hundred-three-module first import root; no object bytes','complete207-module first import root; no object bytes'),
 ('verified 1422 inherited reports and exact source associations','verified1467 inherited complete reports and exact source/object identities')]:
 assert s.count(old)==1,(old,s.count(old));s=s.replace(old,new)
extra="""priorAssembly=DIAG/'transfer-scalar-choice-correspondence-endpoint-20261012-01'
assert not (priorAssembly/'manifest.json').exists() and not list(priorAssembly.glob('*.tar.xz'))
for name in ['prepare_assembly.py','assemble.py']:
 add(priorAssembly/name,'history/unrun-assembly01/'+name,'exact original unrun assembly; inherited status/schema labels corrected before sealing, proof unchanged and not replayed')
"""
at=s.index("add(Path(__file__), 'assemble.py'");s=s[:at]+extra+s[at:]
(ROOT/'assemble.py').write_text(s)
print({'exact_composition_status_and_schema':True,'same_passed6_declarations':True,'all207_module_1467_report_ancestry_preserved':True,'original_unrun_assembly01_retained':True,'no_proof_replay':True})
