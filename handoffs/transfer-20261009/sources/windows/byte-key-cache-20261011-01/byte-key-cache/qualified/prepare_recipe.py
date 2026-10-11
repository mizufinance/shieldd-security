"""Fresh small explicit cache update proof; retain unrun pressure retry plan."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
old=DIAG/'transfer-byte-key-cache-20261011-03'
s=(old/'prepare_recipe.py').read_text().replace('transfer-byte-key-cache-owned-floor-20261011-03','transfer-byte-key-cache-owned-floor-20261011-04')
exec(compile(s,str(old/'prepare_recipe.py'),'exec'),{'__file__':str(ROOT/'prepare_recipe.py'),'__name__':'__main__'})
replacements={
 'fun same => TransferInjectiveKeyPublication01.keyCode_is_injective same':'fun same => @TransferInjectiveKeyPublication01.keyCode_is_injective left right same',
 '  simp only [writeAtBytes, putObject, putByteWrite, encoded_key_equality_iff_exact_byte_key_equality]':'''  change (if keyCode other = keyCode key then some value else delta.cache.objects (keyCode other)) =
    (if other = key then some value else delta.cache.objects (keyCode other))
  by_cases same : other = key
  · rw [if_pos same, if_pos (congrArg keyCode same)]
  · have different : keyCode other ≠ keyCode key := fun equal =>
      same ((encoded_key_equality_iff_exact_byte_key_equality other key).mp equal)
    rw [if_neg same, if_neg different]'''}
for n in ['handwritten/TransferByteKeyCache01.lean','recipe_source.py']:
    p=ROOT/n;s=p.read_text()
    for a,b in replacements.items():assert s.count(a)==1,(n,a,s.count(a));s=s.replace(a,b)
    p.write_text(s)
p=ROOT/'prepare.py';s=p.read_text();at=s.index("plan['artifact_policy']")
s=s[:at]+"unrunByteKey=DIAG/'transfer-byte-key-cache-20261011-03'\nassert not (unrunByteKey/'events.jsonl').exists()\nplan['pins'] += [pin(unrunByteKey/n) for n in ['prepare_recipe.py','recipe_source.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','handwritten/TransferByteKeyCache01.lean','project/ShielddSecurity/TransferByteKeyCache01.lean']]\n"+s[at:]
p.write_text(s)
