from pathlib import Path
import subprocess,sys,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
prior=DIAG/'transfer-scalar-choice-masks-20261012-04'
assert not (ROOT/'prepare.py').exists()
events=[json.loads(s) for s in (prior/'events.jsonl').read_text().splitlines()]
assert events[-1]['result']['reason']=='Lean exit 1'
stdout=(prior/'runs/01-TransferScalarChoiceMasks01/stdout.txt').read_text()
assert '94:8: error: (kernel) excessive memory consumption detected' in stdout
(ROOT/'prepare_recipe_from03.py').write_bytes((prior/'prepare_recipe_from03.py').read_bytes())
subprocess.run([sys.executable,'-B',str(ROOT/'prepare_recipe_from03.py')],check=True)
h=ROOT/'handwritten/TransferScalarChoiceMasks01.lean';s=h.read_text()
needle='def sourceMaskedConstantTimeStep (self current : CanonicalScalar) (bit : Bool) : CanonicalScalar :='
assert s.count(needle)==1
lemma="""theorem exact_source_masked_scalar_boolean_selection_equals_the_boolean_branch
    (a b : CanonicalScalar) (bit : Bool) :
    sourceMaskedScalarSelect a b (sourceChoiceFromBool bit) = if bit then b else a := by
  rw [exact_source_masked_scalar_selection_equals_the_whole_canonical_branch]
  cases bit <;> rfl

"""
s=s.replace(needle,lemma+needle)
old="""  unfold sourceMaskedConstantTimeStep
  rw [exact_source_masked_scalar_selection_equals_the_whole_canonical_branch]
  cases bit <;> rfl"""
new="""  exact exact_source_masked_scalar_boolean_selection_equals_the_boolean_branch
    (sourceCanonicalSquare current) (sourceCanonicalMul (sourceCanonicalSquare current) self) bit"""
assert s.count(old)==1;s=s.replace(old,new)
at=s.index('set_option pp.all true in\n#check @sourceMaskedConstantTimeStep')
audit="""set_option pp.all true in
#check @exact_source_masked_scalar_boolean_selection_equals_the_boolean_branch
#print axioms exact_source_masked_scalar_boolean_selection_equals_the_boolean_branch
"""
s=s[:at]+audit+s[at:];h.write_text(s)
p=ROOT/'prepare.py';s=p.read_text()
assert s.count('assert len(names) == 20')==1
s=s.replace('assert len(names) == 20','assert len(names) == 21').replace("'fresh_audits': 20","'fresh_audits': 21")
s=s.replace('Twenty declarations.','Twenty-one declarations, including an abstract Boolean selection lemma that avoids unfolding generated square/multiply bodies during kernel equality checking.')
extra="""plan['pins'].append(pin(ROOT/'prepare_recipe_from04.py'))
failedChoice=DIAG/'transfer-scalar-choice-masks-20261012-04'
failedFiles=sorted(p for p in failedChoice.rglob('*') if p.is_file())
assert len(failedFiles)==15
plan['pins'] += [pin(p) for p in failedFiles]
for directory,names in [
 ('transfer-scalar-choice-masks-endpoint-20261012-04',['prepare_assembly.py','assemble.py']),
 ('transfer-scalar-choice-masks-checkpoint-20261012-04',['preservation_check.py','preservation.json'])]:
 plan['pins'] += [pin(DIAG/directory/n) for n in names]
"""
at=s.index("plan['artifact_policy']");s=s[:at]+extra+s[at:];p.write_text(s)
print({'fresh_public_declarations':21,'all_original_20_statements_unchanged':True,'one_reusable_boolean_selection_lemma':True,'prior_full_kernel_failure_output_retained':True,'all_guards_unchanged':True})
