import ShielddSecurity.CapturedCanonical216W03
import ShielddSecurity.CapturedCanonical216W04
import ShielddSecurity.CapturedCanonical216W05
import ShielddSecurity.CapturedCanonical216W39
import ShielddSecurity.CapturedCanonical216W42
import ShielddSecurity.CapturedCanonical216W48
import ShielddSecurity.CapturedCanonical216W49
import ShielddSecurity.CapturedCanonical216W50
import ShielddSecurity.CapturedCanonical216W51
import ShielddSecurity.CapturedCanonical216W52
import ShielddSecurity.CapturedCanonical216W53
import ShielddSecurity.CapturedCanonical216W54
import ShielddSecurity.CapturedCanonical216W55
import ShielddSecurity.CapturedCanonical216W58
import ShielddSecurity.CanonicalRecovery195
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CanonicalInputs222
open CompilerAssertionBlock51 CompilerArithmeticTransport41
def columns : List Nat := [11,6,13,9061,10593,1743,1742,1751,1750,1505,1504,1513,1512,20937]
theorem count : columns.length=14 := rfl
variable {F : Type} [Field F] [CharP F p]
theorem recovered (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (one : rho 0=1) : ∀ column∈columns,∃ n : Nat,n<p ∧ (n:F)=rho column := by
 simp only [columns,List.forall_mem_cons]
 exact ⟨CapturedCanonical216W03.sound rho satisfied one,⟨CapturedCanonical216W04.sound rho satisfied one,⟨CapturedCanonical216W05.sound rho satisfied one,⟨CapturedCanonical216W39.sound rho satisfied one,⟨CapturedCanonical216W42.sound rho satisfied one,⟨CapturedCanonical216W48.sound rho satisfied one,⟨CapturedCanonical216W49.sound rho satisfied one,⟨CapturedCanonical216W50.sound rho satisfied one,⟨CapturedCanonical216W51.sound rho satisfied one,⟨CapturedCanonical216W52.sound rho satisfied one,⟨CapturedCanonical216W53.sound rho satisfied one,⟨CapturedCanonical216W54.sound rho satisfied one,⟨CapturedCanonical216W55.sound rho satisfied one,⟨CapturedCanonical216W58.sound rho satisfied one,by intro column member;cases member⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def number (rho : Nat → F) (column : Nat) : Nat := by
 classical
 exact if h : ∃ n : Nat,n<p ∧ (n:F)=rho column then Classical.choose h else 0
theorem number_sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (one : rho 0=1) (column : Nat) (member : column∈columns) :
 number rho column<p ∧ (number rho column:F)=rho column := by
 have h:=recovered rho satisfied one column member
 simp only [number,dif_pos h]
 exact Classical.choose_spec h
theorem unique (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (one : rho 0=1) (column : Nat) (member : column∈columns) (n : Nat)
 (bound : n<p) (meaning : (n:F)=rho column) : number rho column=n :=
 CapturedEpochHints62.cast_small_unique _ n (number_sound rho satisfied one column member).1 bound
 ((number_sound rho satisfied one column member).2.trans meaning.symm)
theorem representation_value (representation : PoseidonNatural192.CanonicalRepresentation F)
 (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (one : rho 0=1) (column : Nat) (member : column∈columns) :
 representation.value (rho column)=number rho column :=
 CanonicalRecovery195.value_unique representation _ _ (number_sound rho satisfied one column member).1
 (number_sound rho satisfied one column member).2
end ShielddSecurity.CanonicalInputs222

set_option pp.all true in
#check @ShielddSecurity.CanonicalInputs222.columns
#print axioms ShielddSecurity.CanonicalInputs222.columns
set_option pp.all true in
#check @ShielddSecurity.CanonicalInputs222.count
#print axioms ShielddSecurity.CanonicalInputs222.count
set_option pp.all true in
#check @ShielddSecurity.CanonicalInputs222.recovered
#print axioms ShielddSecurity.CanonicalInputs222.recovered
set_option pp.all true in
#check @ShielddSecurity.CanonicalInputs222.number
#print axioms ShielddSecurity.CanonicalInputs222.number
set_option pp.all true in
#check @ShielddSecurity.CanonicalInputs222.number_sound
#print axioms ShielddSecurity.CanonicalInputs222.number_sound
set_option pp.all true in
#check @ShielddSecurity.CanonicalInputs222.unique
#print axioms ShielddSecurity.CanonicalInputs222.unique
set_option pp.all true in
#check @ShielddSecurity.CanonicalInputs222.representation_value
#print axioms ShielddSecurity.CanonicalInputs222.representation_value
