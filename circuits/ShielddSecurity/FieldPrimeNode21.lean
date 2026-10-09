-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate
import ShielddSecurity.FieldPrimeNode01
import ShielddSecurity.FieldPrimeNode02
import ShielddSecurity.FieldPrimeNode10

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode21
open LucasCertificate

def certificate : Certificate := ⟨523, 2, [⟨2, 261, 522⟩, ⟨3, 174, 462⟩, ⟨3, 174, 462⟩, ⟨29, 18, 121⟩]⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 523 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate, FieldPrimeNode01.prime, FieldPrimeNode02.prime, FieldPrimeNode10.prime]

end ShielddSecurity.FieldPrimeNode21
