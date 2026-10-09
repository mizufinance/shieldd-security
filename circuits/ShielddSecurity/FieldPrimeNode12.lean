-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate
import ShielddSecurity.FieldPrimeNode01
import ShielddSecurity.FieldPrimeNode09

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode12
open LucasCertificate

def certificate : Certificate := ⟨47, 5, [⟨2, 23, 46⟩, ⟨23, 2, 25⟩]⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 47 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate, FieldPrimeNode01.prime, FieldPrimeNode09.prime]

end ShielddSecurity.FieldPrimeNode12
