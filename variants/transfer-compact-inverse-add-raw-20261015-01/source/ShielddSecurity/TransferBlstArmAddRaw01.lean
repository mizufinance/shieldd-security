import ShielddSecurity.TransferBlstArmCarryChains01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmAdd01
open TransferBlstArmCarryChains01 (sourceAddCarryChain)
attribute [local irreducible] sourceAddCarryChain

def sourceArmAddRaw (left right : Vector UInt64 4) : List UInt64 × Bool :=
  sourceAddCarryChain false (left.toList.zip right.toList)

theorem source_arm_add_raw_retains_four_limbs (left right : Vector UInt64 4) :
    (sourceArmAddRaw left right).1.length = 4 := by
  rw [sourceArmAddRaw,TransferBlstArmCarryChains01.actual_add_chain_retains_the_source_limb_count,
    List.length_zip,Vector.length_toList,Vector.length_toList,Nat.min_self]

set_option pp.all true in
#check @sourceArmAddRaw
#print axioms sourceArmAddRaw
set_option pp.all true in
#check @source_arm_add_raw_retains_four_limbs
#print axioms source_arm_add_raw_retains_four_limbs
end ShielddSecurity.TransferBlstArmAdd01
