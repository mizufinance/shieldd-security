from pathlib import Path
import json,hashlib,sys
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-registry-semantic-sound205-source02';S=W/'mac-registry-semantic-sound205-source03'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated');require(not S.exists(),'immutable');spec=json.loads((P/'templates01.json').read_bytes());d=spec['modules']['RegistrySemanticSound205'];body=d['body'];require(body.count('CapturedRegulatedSound163.role_cases rho satisfied one')==1,'exact flag API');body=body.replace('CapturedRegulatedSound163.role_cases rho satisfied one','CapturedRegulatedSound163.role_cases rho satisfied');body=body.replace('theorem exists_flag (rho : Nat → F) (one : rho 0=1)','theorem exists_flag (rho : Nat → F)');d['body']=body;spec['inputs'][str(P/'templates01.json')]=pin(P/'templates01.json');spec['scope']=dict(historical_scope=spec['scope'],repair='2279 main full_registry elaborated, entire module failed because existing role_cases takes no one argument. Remove extra argument and unnecessary one premise from exists_flag only; full_registry conclusion/premises unchanged',status='SOURCE_ONLY_UNRUN');S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((P/'generate.py').read_bytes());(S/'templates01.json').write_text(json.dumps(spec,sort_keys=True,separators=(',',':'))+'\n')
