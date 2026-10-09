import ShielddSecurity.TransferLongRecipeExpressions01
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.TransferLongRecipeNormalize01
open TransferLongRecipeData01
theorem left_length : (terms leftPort).length=258 := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferLongRecipeNormalize01.left_length
#print axioms ShielddSecurity.TransferLongRecipeNormalize01.left_length
theorem right_length : (terms rightPort).length=2 := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferLongRecipeNormalize01.right_length
#print axioms ShielddSecurity.TransferLongRecipeNormalize01.right_length
end ShielddSecurity.TransferLongRecipeNormalize01
