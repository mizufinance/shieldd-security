-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate
import ShielddSecurity.FieldPrimeNode01
import ShielddSecurity.FieldPrimeNode16

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode18
open LucasCertificate

def certificate : Certificate := ⟨179, 2, [⟨2, 89, 178⟩, ⟨89, 2, 4⟩]⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 179 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate, FieldPrimeNode01.prime, FieldPrimeNode16.prime]

end ShielddSecurity.FieldPrimeNode18
