import ShielddSecurity.RoutingPrecisionLayout808
import ShielddSecurity.FieldZeroSeed125
import ShielddSecurity.TransferSem
import ShielddSecurity.RegistryNaturalSeed298
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RoutingPrecisionSeed811
open ConcreteJubjubField01
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model

def precision (w : TransferSem.Witness) (family : Bool) : Nat :=
  if family then w.routing.unregulatedPrecision else w.routing.regulatedPrecision
def start (family : Bool) : Nat := if family then 19523 else 19457

def seed (original : Nat → F) (w : TransferSem.Witness) (column : Nat) : F :=
  if column=19455 then (w.routing.regulatedPrecision:F)
  else if column=19456 then (w.routing.unregulatedPrecision:F)
  else if 19457≤column ∧ column<19523 then
    let delta := (w.routing.regulatedPrecision:F)-(((column-19457)/2:Nat):F)
    if column%2=1 then FieldZeroSeed125.flag delta else delta⁻¹
  else if 19523≤column ∧ column<19589 then
    let delta := (w.routing.unregulatedPrecision:F)-(((column-19523)/2:Nat):F)
    if column%2=1 then FieldZeroSeed125.flag delta else delta⁻¹
  else original column

theorem regulated (original : Nat → F) (w : TransferSem.Witness) : seed original w 19455=(w.routing.regulatedPrecision:F) := rfl
theorem unregulated (original : Nat → F) (w : TransferSem.Witness) : seed original w 19456=(w.routing.unregulatedPrecision:F) := rfl

theorem flag (original : Nat → F) (w : TransferSem.Witness) (family : Bool) (index : Fin 33) :
    seed original w (start family+2*index.val)=FieldZeroSeed125.flag ((precision w family:F)-(index.val:F)) := by
  have bound := index.isLt
  cases family
  · have division : (19457+2*index.val-19457)/2=index.val := by omega
    have parity : (19457+2*index.val)%2=1 := by omega
    simp only [start,precision,Bool.false_eq_true,if_false,if_true]
    simp only [seed,if_neg (show (19457+2*index.val)≠19455 by omega),if_neg (show (19457+2*index.val)≠19456 by omega),
      if_pos (show 19457≤(19457+2*index.val) ∧ (19457+2*index.val)<19523 by omega),division,parity,
      if_true]
  · have division : (19523+2*index.val-19523)/2=index.val := by omega
    have parity : (19523+2*index.val)%2=1 := by omega
    simp only [start,precision,Bool.false_eq_true,if_false,if_true]
    simp only [seed,if_neg (show (19523+2*index.val)≠19455 by omega),if_neg (show (19523+2*index.val)≠19456 by omega),
      if_neg (show ¬(19457≤(19523+2*index.val) ∧ (19523+2*index.val)<19523) by omega),
      if_pos (show 19523≤(19523+2*index.val) ∧ (19523+2*index.val)<19589 by omega),division,parity,
      if_true]

theorem inverse (original : Nat → F) (w : TransferSem.Witness) (family : Bool) (index : Fin 33) :
    seed original w (start family+2*index.val+1)=((precision w family:F)-(index.val:F))⁻¹ := by
  have bound := index.isLt
  cases family
  · have division : (19457+2*index.val+1-19457)/2=index.val := by omega
    have parity : (19457+2*index.val+1)%2=0 := by omega
    simp only [start,precision,Bool.false_eq_true,if_false,if_true]
    simp only [seed,if_neg (show (19457+2*index.val+1)≠19455 by omega),if_neg (show (19457+2*index.val+1)≠19456 by omega),
      if_pos (show 19457≤(19457+2*index.val+1) ∧ (19457+2*index.val+1)<19523 by omega),division,parity,
      show ¬(0:Nat)=1 by decide,if_false]
  · have division : (19523+2*index.val+1-19523)/2=index.val := by omega
    have parity : (19523+2*index.val+1)%2=0 := by omega
    simp only [start,precision,Bool.false_eq_true,if_false,if_true]
    simp only [seed,if_neg (show (19523+2*index.val+1)≠19455 by omega),if_neg (show (19523+2*index.val+1)≠19456 by omega),
      if_neg (show ¬(19457≤(19523+2*index.val+1) ∧ (19523+2*index.val+1)<19523) by omega),
      if_pos (show 19523≤(19523+2*index.val+1) ∧ (19523+2*index.val+1)<19589 by omega),division,parity,
      show ¬(0:Nat)=1 by decide,if_false]

theorem outside (original : Nat → F) (w : TransferSem.Witness) (column : Nat)
    (separate : column<19455 ∨ 19589≤column) : seed original w column=original column := by
  simp only [seed,if_neg (show column≠19455 by omega),if_neg (show column≠19456 by omega),
    if_neg (show ¬(19457≤column ∧ column<19523) by omega),
    if_neg (show ¬(19523≤column ∧ column<19589) by omega)]

theorem boolean (original : Nat → F) (w : TransferSem.Witness) (column : Nat)
    (member : column∈RoutingPrecisionLayout808.flags) : seed original w column=0 ∨ seed original w column=1 := by
  classical
  obtain ⟨offset,bound,equal⟩ := List.mem_range'.mp member
  rw [equal]
  by_cases first : offset<33
  · change seed original w (start false+2*(⟨offset,first⟩:Fin 33).val)=0 ∨ seed original w (start false+2*(⟨offset,first⟩:Fin 33).val)=1
    rw [flag original w false ⟨offset,first⟩]
    unfold FieldZeroSeed125.flag
    split <;> simp
  · have before : offset-33<33 := by omega
    have shifted : 19457+2*offset=start true+2*(⟨offset-33,before⟩:Fin 33).val := by simp only [start,if_true];omega
    rw [shifted,flag original w true ⟨offset-33,before⟩]
    unfold FieldZeroSeed125.flag
    split <;> simp
end ShielddSecurity.RoutingPrecisionSeed811

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionSeed811.regulated
#print axioms ShielddSecurity.RoutingPrecisionSeed811.regulated

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionSeed811.unregulated
#print axioms ShielddSecurity.RoutingPrecisionSeed811.unregulated

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionSeed811.flag
#print axioms ShielddSecurity.RoutingPrecisionSeed811.flag

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionSeed811.inverse
#print axioms ShielddSecurity.RoutingPrecisionSeed811.inverse

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionSeed811.outside
#print axioms ShielddSecurity.RoutingPrecisionSeed811.outside

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionSeed811.boolean
#print axioms ShielddSecurity.RoutingPrecisionSeed811.boolean
