from pathlib import Path
import argparse,json,hashlib,re,os
root=Path(__file__).resolve().parent;ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();assert not a.output.exists();pending=a.output.with_name(a.output.name+'.pending');assert not pending.exists();dst=pending/'source-root/ShielddSecurity';dst.mkdir(parents=True);inventory={}
args='original u c w legal rkInitial authInitial initial senderInitial receiverInitial'
for level in range(24):
 ci=125+level;cur=f'VolumePathHash931C{ci}';prev='VolumePriorHash908' if level==0 else f'VolumePathHash931C{ci-1}';selector=f'VolumePathSelector945L{level:02d}';name=f'VolumePathLevel948L{level:02d}';lo=8460+2*level;hi=lo+1;sib=8388+3*level
 s=f'''-- GENERATED from maintained path level composition; do not edit.
import ShielddSecurity.{selector}
import ShielddSecurity.VolumePathValues947
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.{name}
open Compiler CompilerAssertionBlock51 TransferSem
open CapturedInitial73419Generic01 (p copy)
attribute [local irreducible] SatisfiesAt ConcreteRegistrySharedEncoding294.model
  VolumePathAssignment942.assignment VolumePathMeaning946.value PoseidonNatural192.hash Poseidon.hash6 volumeState

theorem generic_hash {{G : Type}} [Field G] [CharP G p] (rho : Nat → G)
    (one : rho 0=1) (copied : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) (low high : Bool)
    (node s0 s1 s2 : G)
    (low_value : rho {lo}=BooleanHints207.bitValue low) (high_value : rho {hi}=BooleanHints207.bitValue high)
    (previous : eval rho {prev}.result=node)
    (first : rho {sib}=s0) (second : rho {sib+1}=s1) (third : rho {sib+2}=s2) :
    eval rho {cur}.result=Poseidon.hash6 (Poseidon.castParameters {cur}.parameters) 1
      ([({level+1}:G)]++QuaternarySelector944.children
        (if high then (if low then 3 else 2) else (if low then 1 else 0)) node s0 s1 s2) := by
  have result := {cur}.hash rho one (copied.trans one.symm) arithmetic
  rw [{selector}.input_values rho one arithmetic low high low_value high_value,previous,first,second,third] at result
  exact result

open ConcreteJubjubField01
open VolumePathAssignment942 (assignment)
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)

theorem result (previous : eval (assignment {args}) {prev}.result=
    (VolumePathMeaning946.value (BalanceBlindingDomain670.crypto c) w {level}:F)) :
    eval (assignment {args}) {cur}.result=
      (VolumePathMeaning946.value (BalanceBlindingDomain670.crypto c) w {level+1}:F) := by
  have first : assignment {args} {sib}=(VolumePathMeaning946.siblings w {level} 0:F) := by
    simpa only [VolumePathMeaning946.siblings,dif_pos (show {level}<24 by decide)] using
      VolumePathAssignment942.sibling {args} ⟨{level},by decide⟩ 0
  have second : assignment {args} {sib+1}=(VolumePathMeaning946.siblings w {level} 1:F) := by
    simpa only [VolumePathMeaning946.siblings,dif_pos (show {level}<24 by decide)] using
      VolumePathAssignment942.sibling {args} ⟨{level},by decide⟩ 1
  have third : assignment {args} {sib+2}=(VolumePathMeaning946.siblings w {level} 2:F) := by
    simpa only [VolumePathMeaning946.siblings,dif_pos (show {level}<24 by decide)] using
      VolumePathAssignment942.sibling {args} ⟨{level},by decide⟩ 2
  have joined := generic_hash (assignment {args}) (VolumePathValues947.zero {args})
    (VolumePathValues947.copied {args}) (VolumePathValues947.arithmetic {args})
    ((encodeBits 48 w.volume.priorPosition)[{2*level}]?.getD false)
    ((encodeBits 48 w.volume.priorPosition)[{2*level+1}]?.getD false) _ _ _ _
    (VolumePathBits943.bits {args} {2*level} (by decide))
    (VolumePathBits943.bits {args} {2*level+1} (by decide)) previous first second third
  rw [QuaternarySelector944.encoded_slot w.volume.priorPosition {level} (by decide)] at joined
  rw [show {level+1}={level}+1 from rfl,VolumePathMeaning946.successor]
  have natural := VolumePathMeaning946.natural_hash c {level} (w.volume.priorPosition/4^{level}%4)
    (VolumePathMeaning946.value (BalanceBlindingDomain670.crypto c) w {level})
    (VolumePathMeaning946.siblings w {level} 0) (VolumePathMeaning946.siblings w {level} 1)
    (VolumePathMeaning946.siblings w {level} 2)
  exact joined.trans natural.symm
end ShielddSecurity.{name}
'''

 for n in ['generic_hash','result']:s+=f'\nset_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n'
 f=dst/(name+'.lean');f.write_text(s);inventory[name]=dict(sha256=hashlib.sha256(f.read_bytes()).hexdigest(),audits=['generic_hash','result'])
name='VolumePathLevels948';s=''.join('import ShielddSecurity.'+n+'\n' for n in inventory)+f'namespace ShielddSecurity.{name}\ndef levelCount : Nat := 24\nend ShielddSecurity.{name}\nset_option pp.all true in\n#check @ShielddSecurity.{name}.levelCount\n#print axioms ShielddSecurity.{name}.levelCount\n';f=dst/(name+'.lean');f.write_text(s);inventory[name]=dict(sha256=hashlib.sha256(f.read_bytes()).hexdigest(),audits=['levelCount'])
(pending/'generation.json').write_text(json.dumps(inventory,indent=2,sort_keys=True)+'\n');os.replace(pending,a.output);print(json.dumps(dict(modules=len(inventory),audits=49)))
