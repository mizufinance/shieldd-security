import ShielddSecurity.CapturedMerklePositionGlobal190
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleIntegerRoot191
open Compiler Poseidon
open CapturedInitial73419Generic01 (p copy)
def bitValue (bit : Bool) : Nat := if bit then 1 else 0
theorem bit_value (n : Nat) : bitValue (decide (n%2=1))=n%2 := by
 have bound:=Nat.mod_lt n (by decide : 0<2)
 simp only [bitValue,decide_eq_true_eq]
 split <;> omega
theorem encoded_bit (width n i : Nat) (bound : i<width) :
 (encodeBits width n)[i]'(by simpa only [encodeBits_length] using bound)=decide (n/2^i%2=1) := by
 induction width generalizing n i with
 | zero => omega
 | succ width ih =>
   cases i with
   | zero => simp only [encodeBits,List.getElem_cons_zero,Nat.pow_zero,Nat.div_one]
   | succ i =>
     change (encodeBits width (n/2))[i]=decide (n/2^(i+1)%2=1)
     rw [ih (n/2) i (by omega)]
     simp only [Nat.div_div_eq_div_mul,Nat.pow_succ,Nat.mul_comm]
theorem slot (position : Nat) (level : Fin 16) :
 position/4^level.val%4=
 bitValue (CapturedMerklePositionGlobal190.bits position ⟨2*level.val,by have h:=level.isLt;omega⟩)+
 2*bitValue (CapturedMerklePositionGlobal190.bits position ⟨2*level.val+1,by have h:=level.isLt;omega⟩) := by
 have powers : 2^(2*level.val)=4^level.val := by
   simpa only [Nat.pow_mul] using (rfl : (2^2)^level.val=4^level.val)
 simp only [CapturedMerklePositionGlobal190.bits,encoded_bit,bit_value,powers,Nat.pow_succ]
 rw [←Nat.div_div_eq_div_mul]
 omega
variable {F : Type} [Field F]
def children (slot : Nat) (node a b c : F) (i : Fin 4) : F :=
 (if slot=0 then [node,a,b,c] else if slot=1 then [a,node,b,c]
  else if slot=2 then [a,b,node,c] else [a,b,c,node]).getD i.val 0
theorem children_bits (low high : Bool) (node a b c : F) :
 MerkleQuaternary30.children low high node a b c=children (bitValue low+2*bitValue high) node a b c := by
 cases low <;> cases high <;> rfl
def step (rho : Nat → F) (position : Nat) (level : Fin 16) (node : F) : F :=
 let xs:=children (position/4^level.val%4) node
   (rho (136+3*level.val)) (rho (137+3*level.val)) (rho (138+3*level.val))
 Poseidon.hash6 (castParameters TransferPoseidonCall04Shared01.parameters) 2
   [((level.val+1 : Nat):F),xs 0,xs 1,xs 2,xs 3]
theorem step_eq (rho : Nat → F) (position : Nat) (level : Fin 16) (node : F) :
 MerkleOrdered34.orderedStep rho (CapturedMerklePositionGlobal190.bits position) level node=
 step rho position level node := by
 unfold MerkleOrdered34.orderedStep step
 rw [children_bits,←slot]
def root (rho : Nat → F) (position : Nat) : Nat → F
 | 0 => MerkleInputMeaning28.registryMeaning rho
 | n+1 => step rho position ⟨n%16,Nat.mod_lt n (by decide)⟩ (root rho position n)
theorem root_eq (rho : Nat → F) (position count : Nat) :
 MerkleOrdered34.root rho (CapturedMerklePositionGlobal190.bits position) count=root rho position count := by
 induction count with
 | zero => rfl
 | succ count ih => rw [MerkleOrdered34.root,root,ih,step_eq]
variable [CharP F p]
theorem anchor (rho : Nat → F) (one : rho 0=1)
 (satisfied : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (position : Nat) (canonical : position<p) (meaning : (position:F)=rho 135) :
 position<2^32 ∧ rho 4=root rho position 16 := by
 have observed:=CapturedMerklePositionGlobal190.anchor rho one satisfied position canonical meaning
 exact ⟨observed.1,observed.2.trans (root_eq rho position 16)⟩
end ShielddSecurity.CapturedMerkleIntegerRoot191

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleIntegerRoot191.bitValue
#print axioms ShielddSecurity.CapturedMerkleIntegerRoot191.bitValue
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleIntegerRoot191.bit_value
#print axioms ShielddSecurity.CapturedMerkleIntegerRoot191.bit_value
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleIntegerRoot191.encoded_bit
#print axioms ShielddSecurity.CapturedMerkleIntegerRoot191.encoded_bit
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleIntegerRoot191.slot
#print axioms ShielddSecurity.CapturedMerkleIntegerRoot191.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleIntegerRoot191.children
#print axioms ShielddSecurity.CapturedMerkleIntegerRoot191.children
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleIntegerRoot191.children_bits
#print axioms ShielddSecurity.CapturedMerkleIntegerRoot191.children_bits
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleIntegerRoot191.step
#print axioms ShielddSecurity.CapturedMerkleIntegerRoot191.step
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleIntegerRoot191.step_eq
#print axioms ShielddSecurity.CapturedMerkleIntegerRoot191.step_eq
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleIntegerRoot191.root
#print axioms ShielddSecurity.CapturedMerkleIntegerRoot191.root
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleIntegerRoot191.root_eq
#print axioms ShielddSecurity.CapturedMerkleIntegerRoot191.root_eq
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleIntegerRoot191.anchor
#print axioms ShielddSecurity.CapturedMerkleIntegerRoot191.anchor
