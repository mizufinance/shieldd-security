"""Fresh symbolic equality-chain repair avoids broad constructor unfolding."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
old=DIAG/'transfer-scalar-canonical-key-20261011-01'
assert not (ROOT/'prepare.py').exists()
(ROOT/'handwritten').mkdir()
source=(old/'handwritten/TransferScalarCanonicalKey01.lean').read_text()
start=source.index('  have same : TransferScalarMontgomeryValue01.montgomeryValue')
end=source.index('  exact (TransferCanonicalWordEquality01.canonical_internal_math_values_equal_iff_raw_words_equal',start)
source=source[:start]+'''  have projected : scalarKey (canonicalScalarForKey key).words = scalarKey scalar.words := projection
  have left := TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value
    (canonicalScalarForKey key).words
  have right := TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value scalar.words
  have same : TransferScalarMontgomeryValue01.montgomeryValue (canonicalScalarForKey key).words =
      TransferScalarMontgomeryValue01.montgomeryValue scalar.words := left.symm.trans (projected.trans right)
'''+source[end:]
(ROOT/'handwritten/TransferScalarCanonicalKey01.lean').write_text(source)
s=(old/'prepare.py').read_text().replace('transfer-scalar-canonical-key-owned-floor-20261011-01','transfer-scalar-canonical-key-owned-floor-20261011-02')
s=s.replace("plan['artifact_policy']","failedKey=DIAG/'transfer-scalar-canonical-key-20261011-01'\nplan['pins'] += [pin(failedKey/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarCanonicalKey01.lean','project/ShielddSecurity/TransferScalarCanonicalKey01.lean','runs/01-TransferScalarCanonicalKey01/stdout.txt']]\nplan['artifact_policy']",1)
(ROOT/'prepare.py').write_text(s)
print({'fresh_reports':8,'failed_attempts_preserved':1,'failed_credit':0,'guards_unchanged':True})
