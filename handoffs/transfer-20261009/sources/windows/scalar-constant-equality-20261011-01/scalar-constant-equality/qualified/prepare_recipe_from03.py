from pathlib import Path
import subprocess,sys,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
prior=DIAG/'transfer-scalar-constant-equality-20261012-03'
assert not (ROOT/'prepare.py').exists()
events=[json.loads(s) for s in (prior/'events.jsonl').read_text().splitlines()]
assert events[-1]['result']['reason']=='Lean exit 1'
output=(prior/'runs/01-TransferScalarConstantEquality01/stdout.txt').read_text()
assert '53:10: warning: This simp argument is unused' in output and '89:6: error: Tactic `rewrite` failed' in output
(ROOT/'prepare_recipe_from02.py').write_bytes((prior/'prepare_recipe_from02.py').read_bytes())
subprocess.run([sys.executable,'-B',str(ROOT/'prepare_recipe_from02.py')],check=True)
h=ROOT/'handwritten/TransferScalarConstantEquality01.lean';s=h.read_text()
old='  · simp [UInt64.xor_eq_zero_iff, same]\n  · simp [UInt64.xor_eq_zero_iff, same]'
new='  · simp [same]\n  · simp [UInt64.xor_eq_zero_iff, same]'
assert s.count(old)==1;s=s.replace(old,new)
old='  rw [← exact_four_word_vector_equality_is_all_four_component_equalities]'
new="""  by_cases same : a = b
  · rw [if_pos ((exact_four_word_vector_equality_is_all_four_component_equalities a b).mp same), if_pos same]
  · have different : ¬(a[0] = b[0] ∧ a[1] = b[1] ∧ a[2] = b[2] ∧ a[3] = b[3]) := by
      intro components
      exact same ((exact_four_word_vector_equality_is_all_four_component_equalities a b).mpr components)
    rw [if_neg different, if_neg same]"""
assert s.count(old)==1;s=s.replace(old,new);h.write_text(s)
p=ROOT/'prepare.py';s=p.read_text()
extra="""plan['pins'].append(pin(ROOT/'prepare_recipe_from03.py'))
failedEq=DIAG/'transfer-scalar-constant-equality-20261012-03'
plan['pins'] += [pin(p) for p in sorted(failedEq.rglob('*')) if p.is_file()]
for directory,names in [
 ('transfer-scalar-constant-equality-endpoint-20261012-03',['prepare_assembly.py','assemble.py']),
 ('transfer-scalar-constant-equality-checkpoint-20261012-03',['preservation_check.py','preservation.json'])]:
 plan['pins'] += [pin(DIAG/directory/n) for n in names]
"""
at=s.index("plan['artifact_policy']");s=s[:at]+extra+s[at:];p.write_text(s)
print({'all_12_statements_unchanged':True,'removed_one_unused_simp_argument':True,'dependent_ite_rewrite_replaced_by_explicit_equal_unequal_cases':True,'complete_original_failure_output_retained':True,'all_guards_unchanged':True})
