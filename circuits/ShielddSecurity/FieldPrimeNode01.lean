-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode01
open LucasCertificate

def certificate : Certificate := ⟨2, 1, []⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 2 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate]

end ShielddSecurity.FieldPrimeNode01
