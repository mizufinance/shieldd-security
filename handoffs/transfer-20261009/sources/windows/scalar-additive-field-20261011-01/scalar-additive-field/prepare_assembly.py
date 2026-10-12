from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
prior=DIAG/'transfer-scalar-additive-field-endpoint-20261012-01'
assert not (ROOT/'assemble.py').exists() and not (prior/'manifest.json').exists()
s=(prior/'assemble.py').read_text()
s=s.replace("CURRENT=DIAG/'transfer-scalar-additive-field-20261012-01'","CURRENT=DIAG/'transfer-scalar-additive-field-20261012-02'")
s=s.replace("CHECKPOINT=DIAG/'transfer-scalar-additive-field-checkpoint-20261012-01'","CHECKPOINT=DIAG/'transfer-scalar-additive-field-checkpoint-20261012-02'")
s=s.replace("['prepare.py','prepare_recipe.py'","['prepare.py','prepare_from01.py','prepare_recipe.py'")
extra="""failed=DIAG/'transfer-scalar-additive-field-20261012-01'
failed_event=json.loads((failed/'events.jsonl').read_text().splitlines()[-1]);assert failed_event['result']['status']=='failed'
failed_objects=[]
for p in sorted(failed.rglob('*')):
 if p.is_file():
  assert pin(p) in plan['pins']
  if p.name.endswith(('.olean','.ilean','.o','.c','.olean.private','.olean.server')):
   failed_objects.append(pin(p))
  else:
   add(p,'history/rejected01/'+p.relative_to(failed).as_posix(),'exact rejected unused-range warning, original compiler output/types/axioms and qualification; no passed audit or semantic negative control')
dump(ROOT/'failed-object-identities.json',{'kind':'ORIGINAL_REJECTED_ARTIFACT_IDENTITIES_ONLY','objects':failed_objects,'qualified':False,'scope':'Original compiled artifacts remain immutable on producer host; metadata only in portable archive, no qualification or semantic result inferred from hashes.'})
add(ROOT/'failed-object-identities.json','history/rejected01/object-identities.json','exact retained rejected compiler object identity; object bytes excluded')
prior=DIAG/'transfer-scalar-additive-field-endpoint-20261012-01'
assert not (prior/'manifest.json').exists()
for name in ['prepare_assembly.py','assemble.py']:
 add(prior/name,'history/unrun-assembly01/'+name,'original unrun assembly against first rejected module; corrected before assembly execution, no proof replay')
"""
at=s.index('add(Path(__file__)');s=s[:at]+extra+s[at:]
s=s.replace("'rejected_attempts':0","'rejected_attempts':1")
(ROOT/'assemble.py').write_bytes(s.encode())
print({'strengthened_generic_lemma','same_other7_statements','original_rejected_warning_and_object_identities_preserved','original_unrun_assembly_retained'})
