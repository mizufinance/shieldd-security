import ShielddSecurity.SharedWordWitness221
import ShielddSecurity.SharedSeedBase265
import ShielddSecurity.SharedSeedBatch265B00
import ShielddSecurity.SharedSeedBatch265B01
import ShielddSecurity.SharedSeedBatch265B02
import ShielddSecurity.SharedSeedBatch265B03
import ShielddSecurity.SharedSeedBatch265B04
import ShielddSecurity.SharedSeedBatch265B05
import ShielddSecurity.SharedSeedBatch265B06
import ShielddSecurity.SharedSeedBatch265B07
import ShielddSecurity.SharedSeedWord265
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedSeedShape265
theorem boolean_shape (column : Nat) (member : column∈CapturedBooleanRoot209.columns) : Shape column := by
 have checked : CapturedBooleanRoot209.columns.all (fun c => decide (Shape c))=true := by
   simp only [CapturedBooleanRoot209.columns,CapturedBooleanRoot209.slots,List.map_append,List.all_append,b00,b01,b02,b03,b04,b05,b06,b07,b08,b09,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,b26,b27,b28,b29,b30,b31,b32,b33,b34,b35,b36,b37,b38,b39,b40,b41,b42,b43,b44,b45,b46,b47,b48,b49,b50,b51,b52,b53,b54,b55,b56,b57,Bool.true_and]
 exact of_decide_eq_true (List.all_eq_true.mp checked column member)
theorem seed_shape (column : Nat) (member : column∈SharedWordWitness221.seedColumns) : Shape column := by
 rcases List.mem_append.mp member with boolean|word
 · exact boolean_shape column boolean
 · obtain ⟨slot,present,inside⟩:=List.mem_flatMap.mp word
   have shape:=of_decide_eq_true (List.all_eq_true.mp word_checked slot present)
   obtain ⟨offset,before,equal⟩:=List.mem_range'.mp inside
   simp only [Nat.one_mul] at equal
   rcases shape with ⟨start,width⟩|start
   · right;left;change offset<slot.width at before;omega
   · right;right;omega
end ShielddSecurity.SharedSeedShape265

set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.boolean_shape
#print axioms ShielddSecurity.SharedSeedShape265.boolean_shape
set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.seed_shape
#print axioms ShielddSecurity.SharedSeedShape265.seed_shape
