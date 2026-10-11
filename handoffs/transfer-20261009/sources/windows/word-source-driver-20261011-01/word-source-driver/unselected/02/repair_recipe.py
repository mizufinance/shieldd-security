from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare_recipe.py').exists()
prior=DIAG/'transfer-word-source-driver-20261011-01'
assert not (prior/'events.jsonl').exists() and not (prior/'plan.json').exists()
s=(prior/'prepare_recipe.py').read_text()
s=s.replace('transfer-word-source-driver-owned-floor-20261011-01','transfer-word-source-driver-owned-floor-20261011-02')
s=s.replace("start=s.index(\"stdout = UPSTREAM / \");end=s.index('assert len(records)',start)","replace(\"'imports': ['ShielddSecurity.TransferCanonicalWordPending01']\", \"'imports': ['ShielddSecurity.TransferWordObjectCodec01']\")\nstart=s.index(\"stdout = UPSTREAM / \");end=s.index('assert len(records)',start)")
s=s.replace("at=source.index('set_option pp.all true in\\n#check @installSourceOrderedTaggedIo')", "at=source.index('set_option pp.all true in\\n#check @fresh_absent_source_finalization_publishes_exact_global_mathematical_input_vector')")
s=s.replace("(ROOT/'prepare.py').write_text(s)","s=s.replace(\"plan['artifact_policy'] =\", \"unrunDriver = DIAG/'transfer-word-source-driver-20261011-01'\\nassert not (unrunDriver/'events.jsonl').exists() and not (unrunDriver/'plan.json').exists()\\nplan['pins'] += [pin(unrunDriver/n) for n in ['prepare_recipe.py','prepare.py','handwritten/TransferWordSourceDriver01.lean']]\\nplan['artifact_policy'] =\")\n(ROOT/'prepare.py').write_text(s)")
(ROOT/'prepare_recipe.py').write_text(s)
print({'setup_repair':True,'no_lean_attempt_in_setup01':True})
