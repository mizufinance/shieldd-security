import ShielddSecurity.CapturedWordRoot213
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedSeedShape265
theorem word_checked : (CapturedWordRoot213.words.map Prod.fst).all (fun slot => decide ((slot.start=49 ∧ slot.width=64) ∨ 184≤slot.start))=true := by decide +kernel
end ShielddSecurity.SharedSeedShape265

set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.word_checked
#print axioms ShielddSecurity.SharedSeedShape265.word_checked
