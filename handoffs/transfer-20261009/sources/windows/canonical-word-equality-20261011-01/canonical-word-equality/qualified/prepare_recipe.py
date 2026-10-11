"""Fresh explicit beta-expression repair; preserve all failed raw evidence."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
old=DIAG/'transfer-canonical-word-equality-20261011-01'
s=(old/'prepare_recipe.py').read_text()
a='      rw [packed_word_cons_division_recovers_exact_tail, packed_word_cons_division_recovers_exact_tail] at tails'
b='      change packWords (head :: rest) / radix64 = packWords (other :: tail) / radix64 at tails\n'+a
assert s.count(a)==1;s=s.replace(a,b)
a='    rw [leftRelation, rightRelation, Nat.mod_eq_of_lt left.canonical, Nat.mod_eq_of_lt right.canonical] at packed'
b='    change (radix64 ^ 4 * montgomeryValue left.words) % nullifierModulus = (radix64 ^ 4 * montgomeryValue right.words) % nullifierModulus at packed\n'+a
assert s.count(a)==1;s=s.replace(a,b).replace('transfer-canonical-word-equality-owned-floor-20261011-01','transfer-canonical-word-equality-owned-floor-20261011-02')
(ROOT/'recipe_source.py').write_text(s)
exec(compile(s,str(ROOT/'recipe_source.py'),'exec'),{'__file__':str(ROOT/'recipe_source.py'),'__name__':'__main__'})
p=ROOT/'prepare.py';s=p.read_text();a="[Path(__file__), ROOT / 'prepare_recipe.py', runner";assert s.count(a)==1
s=s.replace(a,"[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner")
at=s.index("plan['artifact_policy']")
s=s[:at]+"failedCanonical=DIAG/'transfer-canonical-word-equality-20261011-01'\nplan['pins'] += [pin(failedCanonical/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferCanonicalWordEquality01.lean','project/ShielddSecurity/TransferCanonicalWordEquality01.lean','runs/01-TransferCanonicalWordEquality01/stdout.txt']]\n"+s[at:]
p.write_text(s)
