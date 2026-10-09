import ShielddSecurity.TransferLongRecipeRecords01
namespace ShielddSecurity.TransferLongRecipeTableShape01
open TransferLongRecipeData01
theorem table_size : records.size=1036 := by decide +kernel
end ShielddSecurity.TransferLongRecipeTableShape01
set_option pp.all true in
#check @ShielddSecurity.TransferLongRecipeTableShape01.table_size
#print axioms ShielddSecurity.TransferLongRecipeTableShape01.table_size
