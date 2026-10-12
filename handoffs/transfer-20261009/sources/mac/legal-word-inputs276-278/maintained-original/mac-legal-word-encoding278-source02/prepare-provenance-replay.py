from pathlib import Path
import sys,json,hashlib
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');A=W/'mac-legal-alias-meanings276-source01';N=W/'mac-legal-alias-meanings276-source02';B=W/'mac-legal-word-encoding278-source01';T=Path(__file__).resolve().parent
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated provenance replay')
provenance=json.loads((T/'provenance01.json').read_bytes());require(pin(B/'templates01.json')==provenance['old_templates'],'exact maintained old templates');require(pin(N/'source-root/ShielddSecurity/LegalAliasMeanings276.lean')==provenance['new_276'],'exact repaired source');d=json.loads((B/'templates01.json').read_bytes());require(d['inputs'].pop(str(A/'source-root/ShielddSecurity/LegalAliasMeanings276.lean'))==provenance['old_276'],'exact old source provenance');d['inputs'][str(N/'source-root/ShielddSecurity/LegalAliasMeanings276.lean')]=provenance['new_276'];d['inputs'][str(B/'templates01.json')]=provenance['old_templates'];d['scope']['provenance_successor']='All5 mathematical bodies and71 planned audit names unchanged; import source pin now exact maintained276 source02 repair. Original unrun source27801 preserved.';encoded=(json.dumps(d,sort_keys=True,separators=(',',':'))+'\n').encode();require(encoded==(T/'templates01.json').read_bytes(),'exact maintained provenance byte replay');print(json.dumps(dict(bytes=len(encoded),sha256=hashlib.sha256(encoded).hexdigest(),scope='Pure provenance replay only; five mathematical bodies and audit names unchanged, no Lean.')))
