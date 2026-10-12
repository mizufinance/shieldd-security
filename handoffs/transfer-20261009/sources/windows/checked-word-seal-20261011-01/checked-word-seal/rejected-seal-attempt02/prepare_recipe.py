from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-checked-word-seal-20261011-01'
assert not (ROOT/'prepare.py').exists()
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-checked-word-seal-owned-floor-20261011-01'","POOL = DIAG / 'transfer-checked-word-seal-owned-floor-20261011-02'")
at=s.index("plan['artifact_policy'] = ")
s=s[:at]+"lintSeal=DIAG/'transfer-checked-word-seal-20261011-01'\nplan['pins'] += [pin(lintSeal/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/checked-word-seal-shape.json','handwritten/TransferCheckedWordSeal01.lean','project/ShielddSecurity/TransferCheckedWordSeal01.lean','runs/01-TransferCheckedWordSeal01/stdout.txt','project/ShielddSecurity/TransferCheckedWordSeal01.olean']]\nplan['pins'].append(pin(ROOT/'rejected-object-identity.json'))\n"+s[at:]
source=(OLD/'handwritten/TransferCheckedWordSeal01.lean').read_text()
assert source.count('∃ ordered members : List CanonicalScalar,')==1
source=source.replace('∃ ordered members : List CanonicalScalar,','∃ ordered _members : List CanonicalScalar,')
(ROOT/'handwritten').mkdir();(ROOT/'context').mkdir()
(ROOT/'handwritten/TransferCheckedWordSeal01.lean').write_text(source)
(ROOT/'context/checked-word-seal-shape.json').write_bytes((OLD/'context/checked-word-seal-shape.json').read_bytes())
obj=OLD/'project/ShielddSecurity/TransferCheckedWordSeal01.olean';b=obj.read_bytes()
(ROOT/'rejected-object-identity.json').write_text(json.dumps({'original':{'path':str(obj),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()},'scope':'Entire original warning attempt zero proof credit; object not imported or included in portable archive, identity only.'},indent=2)+'\n')
(ROOT/'prepare.py').write_text(s)
print({'unused_existential_binder_renamed_only':True,'failed_raw_files':11,'failed_object_identity_only':True,'guards_unchanged':True})
