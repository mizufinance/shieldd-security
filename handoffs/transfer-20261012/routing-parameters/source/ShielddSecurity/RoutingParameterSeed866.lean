import ShielddSecurity.RoutingParameterLayout863
import ShielddSecurity.RegistryNaturalSeed298
import ShielddSecurity.TransferSem
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RoutingParameterSeed866
open ConcreteJubjubField01
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model
def seed (original : Nat → F) (w : TransferSem.Witness) (column : Nat) : F :=
  if column=19589 then (w.routing.parameterSet:F) else if column=19590 then (w.routing.height:F) else original column
theorem parameter_set (original : Nat → F) (w : TransferSem.Witness) : seed original w 19589=(w.routing.parameterSet:F) := rfl
theorem height (original : Nat → F) (w : TransferSem.Witness) : seed original w 19590=(w.routing.height:F) := by
  simp only [seed,show ¬(19590:Nat)=19589 by decide,if_false,if_true]
theorem outside (original : Nat → F) (w : TransferSem.Witness) (column : Nat)
    (separate : column<19589 ∨ 19591≤column) : seed original w column=original column := by
  simp only [seed,if_neg (show column≠19589 by omega),if_neg (show column≠19590 by omega)]
theorem boolean (original : Nat → F) (w : TransferSem.Witness) (column : Nat)
    (member : column∈RoutingParameterLayout863.flags) : seed original w column=0 ∨ seed original w column=1 := by
  simp only [RoutingParameterLayout863.flags,List.not_mem_nil] at member
end ShielddSecurity.RoutingParameterSeed866

set_option pp.all true in
#check @ShielddSecurity.RoutingParameterSeed866.parameter_set
#print axioms ShielddSecurity.RoutingParameterSeed866.parameter_set

set_option pp.all true in
#check @ShielddSecurity.RoutingParameterSeed866.height
#print axioms ShielddSecurity.RoutingParameterSeed866.height

set_option pp.all true in
#check @ShielddSecurity.RoutingParameterSeed866.outside
#print axioms ShielddSecurity.RoutingParameterSeed866.outside

set_option pp.all true in
#check @ShielddSecurity.RoutingParameterSeed866.boolean
#print axioms ShielddSecurity.RoutingParameterSeed866.boolean
