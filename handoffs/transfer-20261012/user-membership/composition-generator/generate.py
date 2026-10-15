from pathlib import Path
import argparse,json,hashlib,os
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();assert not a.output.exists();pending=a.output.with_name(a.output.name+'.pending');assert not pending.exists();dst=pending/'source-root/ShielddSecurity';dst.mkdir(parents=True);inventory={}
args='original u c w legal rkInitial authInitial initial senderInitial receiverInitial'
header='''set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
'''
body='''open Compiler CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open VolumePathAssignment942 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model
  UserTreeMeaning965.value PoseidonNatural192.hash Poseidon.hash6 userLeaf
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
'''
def emit(name,text,names):
 for n in names:text+=f'\nset_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n'
 p=dst/(name+'.lean');p.write_text('-- GENERATED from maintained bounded user path composition; do not edit.\n'+text);inventory[name]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),audits=names)
for user,who,leaf in [('S','sender',21),('R','receiver',38)]:
 for block in range(4):
  start=4*block;end=start+4;name=f'UserPathComposition967{user}B{block:02d}'
  s=''.join(f'import ShielddSecurity.UserPathLevel966{user}L{i:02d}\n' for i in range(start,end))+header+f'namespace ShielddSecurity.{name}\n'+body
  s+=f'theorem result (previous : eval (assignment {args}) UserPathHash958C{leaf+start}.result=(UserTreeMeaning965.value (BalanceBlindingDomain670.crypto c) w.asset w.{who} {start}:F)) :\n    eval (assignment {args}) UserPathHash958C{leaf+end}.result=(UserTreeMeaning965.value (BalanceBlindingDomain670.crypto c) w.asset w.{who} {end}:F) := by\n'
  for i in range(start,end):s+=f'  have h{i+1} := UserPathLevel966{user}L{i:02d}.result {args} '+('previous' if i==start else f'h{i}')+'\n'
  s+=f'  exact h{end}\nend ShielddSecurity.{name}\n';emit(name,s,['result'])
name='UserPathComposition967';s=''.join(f'import ShielddSecurity.UserPathComposition967{user}B{i:02d}\n' for user in ['S','R'] for i in range(4))+'import ShielddSecurity.UserLeafMeaning963\n'+header+f'namespace ShielddSecurity.{name}\n'+body
for user,who,leaf in [('S','sender',21),('R','receiver',38)]:
 s+=f'''theorem {who} : eval (assignment {args}) UserPathHash958C{leaf+16}.result=
    (root (BalanceBlindingDomain670.crypto c) .compliance w.{who}.position
      (userLeaf (BalanceBlindingDomain670.crypto c) w.asset w.{who}) w.{who}.siblings:F) := by
  have leaf := UserLeafMeaning963.hash{leaf} {args}
  have h0 := leaf.trans (congrArg (fun n : Nat => (n:F)) (UserTreeMeaning965.zero (BalanceBlindingDomain670.crypto c) w.asset w.{who}).symm)
'''
 for i in range(4):s+=f'  have h{i+1} := UserPathComposition967{user}B{i:02d}.result {args} h{i}\n'
 s+=f'  exact h4.trans (congrArg (fun n : Nat => (n:F)) (UserTreeMeaning965.final _ w.asset w.{who}))\n'
s+=f'end ShielddSecurity.{name}\n';emit(name,s,['sender','receiver'])
(pending/'generation.json').write_text(json.dumps(inventory,indent=2,sort_keys=True)+'\n');os.replace(pending,a.output);print(json.dumps(dict(modules=len(inventory),audits=sum(len(v['audits']) for v in inventory.values()))))
