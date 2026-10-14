import ShielddSecurity.SemanticCopiesLayout795
import ShielddSecurity.TransferSem
import ShielddSecurity.ConcreteJubjubField01
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SemanticCopiesSeed798
open ConcreteJubjubField01

def value (w : TransferSem.Witness) (column : Nat) : F :=
  if column=4790 ∨ column=4921 then ((w.outputs 0).recovery.commitment:F)
  else if column=6195 ∨ column=6325 then ((w.outputs 1).recovery.commitment:F)
  else (w.timestamp:F)

def seed (original : Nat → F) (w : TransferSem.Witness) (column : Nat) : F :=
  if column∈SemanticCopiesLayout795.values then value w column else original column

theorem selected (original : Nat → F) (w : TransferSem.Witness) (column : Nat)
    (inside : SemanticCopiesLayout795.Inside column) : seed original w column=value w column := if_pos inside

theorem outside (original : Nat → F) (w : TransferSem.Witness) (column : Nat)
    (outside : ¬SemanticCopiesLayout795.Inside column) : seed original w column=original column := if_neg outside
end ShielddSecurity.SemanticCopiesSeed798

set_option pp.all true in
#check @ShielddSecurity.SemanticCopiesSeed798.value
#print axioms ShielddSecurity.SemanticCopiesSeed798.value

set_option pp.all true in
#check @ShielddSecurity.SemanticCopiesSeed798.selected
#print axioms ShielddSecurity.SemanticCopiesSeed798.selected

set_option pp.all true in
#check @ShielddSecurity.SemanticCopiesSeed798.outside
#print axioms ShielddSecurity.SemanticCopiesSeed798.outside
