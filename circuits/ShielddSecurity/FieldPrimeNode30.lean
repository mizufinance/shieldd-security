-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate
import ShielddSecurity.FieldPrimeNode01
import ShielddSecurity.FieldPrimeNode02
import ShielddSecurity.FieldPrimeNode26

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode30
open LucasCertificate

def certificate : Certificate := ⟨859267, 2, [⟨2, 429633, 859266⟩, ⟨3, 286422, 119571⟩, ⟨3, 286422, 119571⟩, ⟨47737, 18, 262144⟩]⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 859267 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate, FieldPrimeNode01.prime, FieldPrimeNode02.prime, FieldPrimeNode26.prime]

end ShielddSecurity.FieldPrimeNode30
