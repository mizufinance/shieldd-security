-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate
import ShielddSecurity.FieldPrimeNode01
import ShielddSecurity.FieldPrimeNode02

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode04
open LucasCertificate

def certificate : Certificate := ⟨7, 3, [⟨2, 3, 6⟩, ⟨3, 2, 2⟩]⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 7 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate, FieldPrimeNode01.prime, FieldPrimeNode02.prime]

end ShielddSecurity.FieldPrimeNode04
