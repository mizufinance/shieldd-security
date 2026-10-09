-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate
import ShielddSecurity.FieldPrimeNode01
import ShielddSecurity.FieldPrimeNode02

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode06
open LucasCertificate

def certificate : Certificate := ⟨13, 2, [⟨2, 6, 12⟩, ⟨2, 6, 12⟩, ⟨3, 4, 3⟩]⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 13 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate, FieldPrimeNode01.prime, FieldPrimeNode02.prime]

end ShielddSecurity.FieldPrimeNode06
