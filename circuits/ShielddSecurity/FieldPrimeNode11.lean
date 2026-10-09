-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate
import ShielddSecurity.FieldPrimeNode01
import ShielddSecurity.FieldPrimeNode02
import ShielddSecurity.FieldPrimeNode04

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode11
open LucasCertificate

def certificate : Certificate := ⟨43, 3, [⟨2, 21, 42⟩, ⟨3, 14, 36⟩, ⟨7, 6, 41⟩]⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 43 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate, FieldPrimeNode01.prime, FieldPrimeNode02.prime, FieldPrimeNode04.prime]

end ShielddSecurity.FieldPrimeNode11
