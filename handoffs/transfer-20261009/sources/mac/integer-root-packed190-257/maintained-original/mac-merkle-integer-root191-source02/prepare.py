from pathlib import Path
import sys,json,hashlib
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-merkle-integer-root191-source01';S=W/'mac-merkle-integer-root191-source02'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated');require(not S.exists(),'immutable');spec=json.loads((P/'templates01.json').read_bytes());d=spec['modules']['CapturedMerkleIntegerRoot191'];body=d['body'];body=body.replace('change (encodeBits width (n/2))[i]=','change (encodeBits width (n/2))[i]\'(by rw [encodeBits_length];omega)=')
a=body.index(' have powers :');b=body.index('variable {F : Type}',a)
body=body[:a]+''' have lowBound : 2*level.val<32 := by have h:=level.isLt;omega
 have highBound : 2*level.val+1<32 := by have h:=level.isLt;omega
 change position/4^level.val%4=
   bitValue ((encodeBits 32 position)[2*level.val]'(by rw [encodeBits_length];exact lowBound))+
   2*bitValue ((encodeBits 32 position)[2*level.val+1]'(by rw [encodeBits_length];exact highBound))
 rw [encoded_bit 32 position (2*level.val) lowBound,
   encoded_bit 32 position (2*level.val+1) highBound,bit_value,bit_value]
 have powers : 2^(2*level.val)=4^level.val := Nat.pow_mul 2 2 level.val
 rw [Nat.pow_succ,powers,←Nat.div_div_eq_div_mul]
 omega
'''+body[b:];d['body']=body;spec['inputs'][str(P/'templates01.json')]=pin(P/'templates01.json');target=W/'mac-merkle-position-global190-source02/source-root/ShielddSecurity/CapturedMerklePositionGlobal190.lean';spec['inputs']={p:v for p,v in spec['inputs'].items()if not p.endswith('/CapturedMerklePositionGlobal190.lean')};spec['inputs'][str(target)]=pin(target);spec['scope']=dict(historical_scope=spec['scope'],repair='2269 actual missing getElem bound and slot simplification failure; explicit index proofs and exact encoded_bit rewrites plus symbolic pow_mul, unchanged conclusions',status='SOURCE_ONLY_UNRUN');S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((P/'generate.py').read_bytes());(S/'templates01.json').write_text(json.dumps(spec,sort_keys=True,separators=(',',':'))+'\n')
