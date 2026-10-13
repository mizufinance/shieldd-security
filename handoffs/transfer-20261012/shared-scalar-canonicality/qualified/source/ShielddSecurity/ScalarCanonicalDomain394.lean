import ShielddSecurity.EncodedWordBits375
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.ScalarCanonicalDomain394
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def values : List Nat := [3766,4930,6334,8551,10083,11611,13629,14891,16153]

theorem inside_checked : values.all (fun column => decide (column∈SemanticWordFrame373.values)) = true := by decide +kernel

theorem inside (column : Nat) (member : column∈values) : SemanticWordFrame373.Inside column := by
  change column∈SemanticWordFrame373.values
  exact of_decide_eq_true (List.all_eq_true.mp inside_checked column member)

theorem widths_checked : values.all (fun column => decide (EncodedWordBits375.width column=252)) = true := by decide +kernel

theorem scalar_bound (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) (column : Nat) (member : column∈values) :
    EncodedWordBits375.value w column<TransferCore.scalarOrder := by
  rcases legal.2.1.2.2.2.1 with ⟨_,_,_,_,_,_,_,_,random,_,_,_⟩
  have outputs := legal.2.1.2.2.2.2.2.1
  have encryption := legal.2.1.2.2.2.2.2.2.2.2.1
  simp only [values,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact random
  · exact (outputs 0).2.2.2.1
  · exact (outputs 1).2.2.2.1
  · exact (encryption.2.2.2.2.2.2.1 0).1
  · exact (encryption.2.2.2.2.2.2.1 1).1
  · exact (encryption.2.2.2.2.2.2.1 2).1
  · exact (encryption.2.2.2.2.2.2.1 3).1
  · exact (encryption.2.2.2.2.2.2.2 0).1
  · exact (encryption.2.2.2.2.2.2.2 1).1

end ShielddSecurity.ScalarCanonicalDomain394

set_option pp.all true in
#check @ShielddSecurity.ScalarCanonicalDomain394.values
#print axioms ShielddSecurity.ScalarCanonicalDomain394.values

set_option pp.all true in
#check @ShielddSecurity.ScalarCanonicalDomain394.inside_checked
#print axioms ShielddSecurity.ScalarCanonicalDomain394.inside_checked

set_option pp.all true in
#check @ShielddSecurity.ScalarCanonicalDomain394.inside
#print axioms ShielddSecurity.ScalarCanonicalDomain394.inside

set_option pp.all true in
#check @ShielddSecurity.ScalarCanonicalDomain394.widths_checked
#print axioms ShielddSecurity.ScalarCanonicalDomain394.widths_checked

set_option pp.all true in
#check @ShielddSecurity.ScalarCanonicalDomain394.scalar_bound
#print axioms ShielddSecurity.ScalarCanonicalDomain394.scalar_bound
