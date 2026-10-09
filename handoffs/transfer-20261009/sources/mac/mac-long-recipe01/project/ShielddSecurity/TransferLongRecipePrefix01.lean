import ShielddSecurity.TransferLongRecipeRecords01
namespace ShielddSecurity.TransferLongRecipePrefix01
open CompilerRecipe01 TransferLongRecipeData01
theorem first_chunk : checkRecords 22735 recordsChunk0=true := by decide +kernel
end ShielddSecurity.TransferLongRecipePrefix01
set_option pp.all true in
#check @ShielddSecurity.TransferLongRecipePrefix01.first_chunk
#print axioms ShielddSecurity.TransferLongRecipePrefix01.first_chunk
