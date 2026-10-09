-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate
import ShielddSecurity.FieldPrimeNode01
import ShielddSecurity.FieldPrimeNode02

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode17
open LucasCertificate

def certificate : Certificate := ⟨97, 5, [⟨2, 48, 96⟩, ⟨2, 48, 96⟩, ⟨2, 48, 96⟩, ⟨2, 48, 96⟩, ⟨2, 48, 96⟩, ⟨3, 32, 35⟩]⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 97 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate, FieldPrimeNode01.prime, FieldPrimeNode02.prime]

end ShielddSecurity.FieldPrimeNode17
