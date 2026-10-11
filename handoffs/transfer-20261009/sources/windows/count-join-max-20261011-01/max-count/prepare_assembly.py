"""Exact source regeneration and zero-credit rejected history for max-count join."""
from pathlib import Path
import shutil, subprocess, hashlib, json
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
CURRENT=DIAG/'transfer-ordinary-max-count-20261011-02'
REGEN=DIAG/'transfer-ordinary-max-count-regeneration-20261011-03'
PRIOR_ENDPOINT=DIAG/'transfer-ordinary-max-count-endpoint-20261011-01'
assert not (ROOT/'assemble.py').exists() and not REGEN.exists()
REGEN.mkdir(); shutil.copyfile(CURRENT/'generate.py',REGEN/'generate.py')
run=subprocess.run(['C:/Users/acyrn/AppData/Local/Programs/Python/Python313/python.exe',str(REGEN/'generate.py')],capture_output=True,check=True)
original=CURRENT/'generated/TransferOrdinaryMaxCount01.lean'; copied=REGEN/'generated/TransferOrdinaryMaxCount01.lean'
assert original.read_bytes()==copied.read_bytes()
def pin(p):
    b=p.read_bytes(); return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
(ROOT/'regeneration.json').write_text(json.dumps({'byte_exact':True,'original':pin(original),'regenerated':pin(copied),'generator':pin(CURRENT/'generate.py'),'copied_generator':pin(REGEN/'generate.py'),'stdout':run.stdout.decode(),'proof_credit':0},indent=2,sort_keys=True)+'\n')
s=(PRIOR_ENDPOINT/'assemble.py').read_text()
s=s.replace('transfer-ordinary-max-count-20261011-01','transfer-ordinary-max-count-20261011-02')
s=s.replace('transfer-ordinary-max-count-checkpoint-20261011-01','transfer-ordinary-max-count-checkpoint-20261011-02')
before="add(ROOT / 'prepare_assembly_derived.py', 'prepare_assembly_derived.py', 'exact derived assembly generator and regeneration recipe')"
assert s.count(before)==1
s=s.replace(before,"add(DIAG / 'transfer-ordinary-max-count-endpoint-20261011-01/prepare_assembly_derived.py', 'predecessor-prepare_assembly_derived.py', 'original unexecuted sealer derivation; no proof credit')")
before="add(ROOT / 'prepare_assembly.py', 'prepare_assembly.py', 'exact assembly derivation source')"
assert s.count(before)==1
extra="""REJECTED = DIAG / 'transfer-ordinary-max-count-20261011-01'
history = [json.loads(x) for x in (REJECTED / 'events.jsonl').read_text().splitlines()]
assert len(history) == 2 and history[-1]['result']['status'] == 'failed'
import re
old = (REJECTED / ('generated/' + MODULE + '.lean')).read_text()
new = (CURRENT / ('generated/' + MODULE + '.lean')).read_text()
def signatures(text):
    return [text[match.start():text.index(' :=',match.start())] for match in re.finditer(r'^theorem ',text,re.M)]
assert signatures(old) == signatures(new) and len(signatures(new)) == 5
assert re.findall(r'^def [^\\n]+',old,re.M) == re.findall(r'^def [^\\n]+',new,re.M)
for name in ['generate.py','prepare.py','prepare_recipe.py','plan.json','review.json','source-mapping.json','events.jsonl','execute_bounded.py','generated/' + MODULE + '.lean','project/ShielddSecurity/' + MODULE + '.lean','runs/01-' + MODULE + '/stdout.txt']:
    add(REJECTED / name, 'rejected-01/' + name, 'original compiler failure; whole attempt zero credit')
"""
s=s.replace(before,extra+'\n'+before)
s=s.replace("'rejected_attempts': 0, 'rejected_proof_credit': 0", "'rejected_attempts': 1, 'rejected_proof_credit': 0")
s=s.replace('All six declarations have complete type/axiom reports, and generated source was independently reproduced in a fresh owned directory.', 'All six declarations have complete type/axiom reports; one definition and five theorem conclusions are identical to the rejected predecessor. The maintained generator fixed only a codec projection proof step, and successful generated source was independently reproduced byte-exact in a fresh owned directory. The rejected compiler attempt retains zero credit.')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':6,'inherited_reports':277,'owned_modules':24,'rejected_credit':0,'regeneration_byte_exact':True})
