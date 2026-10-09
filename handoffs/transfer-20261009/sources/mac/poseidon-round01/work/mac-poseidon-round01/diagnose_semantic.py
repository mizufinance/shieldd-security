from pathlib import Path
import hashlib,json,os
S=Path(__file__).resolve().parent;P=S/'project/ShielddSecurity';O=S.parents[1]/'outputs/mac-poseidon-round01'
for r in (1,4):
 tag=f'{r:02d}';ns=f'ShielddSecurity.TransferPoseidonRound{tag}SemanticChecks01'
 s=f'import ShielddSecurity.TransferPoseidonRound{tag}SemanticData01\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnamespace {ns}\nopen Compiler CompilerIndexed01 Poseidon PoseidonIndexedRound01 TransferPoseidonRound{tag} TransferPoseidonRound{tag}SemanticData01\n'
 for i in range(6):
  s+=f'theorem column{i}_checked : checkColumn p copy originalRows parameters {r} before shifted transformed fifthHints ⟨{i},by decide⟩=true := by decide +kernel\nset_option pp.all true in\n#check @{ns}.column{i}_checked\n#print axioms {ns}.column{i}_checked\n'
 for i in range(6):
  s+=f'theorem mix{i}_checked : canonical p (after ⟨{i},by decide⟩)=canonical p (mixLinear parameters.mds transformed ⟨{i},by decide⟩) := by decide +kernel\nset_option pp.all true in\n#check @{ns}.mix{i}_checked\n#print axioms {ns}.mix{i}_checked\n'
 s+=f'end {ns}\n';p=P/f'TransferPoseidonRound{tag}SemanticChecks01.lean';p.write_text(s)
 print(json.dumps(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())))
