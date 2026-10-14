from pathlib import Path
import json,hashlib,argparse,os
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();assert not a.output.exists();pending=a.output.with_name(a.output.name+'.pending');assert not pending.exists();dst=pending/'source-root/ShielddSecurity';dst.mkdir(parents=True);inventory={}
args='original u c w legal rkInitial authInitial initial senderInitial receiverInitial'
header="""set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
"""
body="""open Compiler CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open VolumePathAssignment942 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model
  VolumePathMeaning946.value PoseidonNatural192.hash Poseidon.hash6 volumeState
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
"""
def emit(name,s,names):
 for n in names:s+=f'\nset_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n'
 p=dst/(name+'.lean');p.write_text('-- GENERATED from maintained bounded path composition; do not edit.\n'+s);inventory[name]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),audits=names)
for block in range(4):
 start=6*block;end=start+6;name=f'VolumePathComposition949B{block:02d}';prev='VolumePriorHash908' if start==0 else f'VolumePathHash931C{124+start}'
 s=''.join(f'import ShielddSecurity.VolumePathLevel948L{i:02d}\n' for i in range(start,end))+header+f'namespace ShielddSecurity.{name}\n'+body
 s+=f'theorem result (previous : eval (assignment {args}) {prev}.result=(VolumePathMeaning946.value (BalanceBlindingDomain670.crypto c) w {start}:F)) :\n    eval (assignment {args}) VolumePathHash931C{124+end}.result=(VolumePathMeaning946.value (BalanceBlindingDomain670.crypto c) w {end}:F) := by\n'
 for i in range(start,end):s+=f'  have h{i+1} := VolumePathLevel948L{i:02d}.result {args} '+('previous' if i==start else f'h{i}')+'\n'
 s+=f'  exact h{end}\nend ShielddSecurity.{name}\n';emit(name,s,['result'])
name='VolumePathComposition949';s=''.join(f'import ShielddSecurity.VolumePathComposition949B{i:02d}\n' for i in range(4))+header+f'namespace ShielddSecurity.{name}\n'+body
s+=f"""theorem result : eval (assignment {args}) VolumePathHash931C148.result=
    (root (BalanceBlindingDomain670.crypto c) .state w.volume.priorPosition
      (volumeState (BalanceBlindingDomain670.crypto c) w.volume.subject w.volume.dayStart w.volume.prior w.volume.priorBlinding)
      w.volume.priorSiblings:F) := by
  have h0 := VolumePathValues947.prior {args}
"""
for i in range(4):s+=f'  have h{i+1} := VolumePathComposition949B{i:02d}.result {args} h{i}\n'
s+='  exact h4.trans (congrArg (fun n : Nat => (n:F)) (VolumePathMeaning946.final _ w))\n'+f'end ShielddSecurity.{name}\n';emit(name,s,['result'])
(pending/'generation.json').write_text(json.dumps(inventory,indent=2,sort_keys=True)+'\n');os.replace(pending,a.output);print(json.dumps(dict(modules=5,audits=5)))
