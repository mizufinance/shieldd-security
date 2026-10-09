-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate
import ShielddSecurity.FieldPrimeNode01
import ShielddSecurity.FieldPrimeNode02
import ShielddSecurity.FieldPrimeNode06

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode15
open LucasCertificate

def certificate : Certificate := ⟨79, 3, [⟨2, 39, 78⟩, ⟨3, 26, 23⟩, ⟨13, 6, 18⟩]⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 79 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate, FieldPrimeNode01.prime, FieldPrimeNode02.prime, FieldPrimeNode06.prime]

end ShielddSecurity.FieldPrimeNode15
