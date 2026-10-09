-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate
import ShielddSecurity.FieldPrimeNode01
import ShielddSecurity.FieldPrimeNode04

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode20
open LucasCertificate

def certificate : Certificate := ⟨449, 3, [⟨2, 224, 448⟩, ⟨2, 224, 448⟩, ⟨2, 224, 448⟩, ⟨2, 224, 448⟩, ⟨2, 224, 448⟩, ⟨2, 224, 448⟩, ⟨7, 64, 324⟩]⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 449 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate, FieldPrimeNode01.prime, FieldPrimeNode04.prime]

end ShielddSecurity.FieldPrimeNode20
