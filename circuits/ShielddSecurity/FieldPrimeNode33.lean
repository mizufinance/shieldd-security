-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate
import ShielddSecurity.FieldPrimeNode01
import ShielddSecurity.FieldPrimeNode02
import ShielddSecurity.FieldPrimeNode09
import ShielddSecurity.FieldPrimeNode24

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode33
open LucasCertificate

def certificate : Certificate := ⟨2529403, 2, [⟨2, 1264701, 2529402⟩, ⟨3, 843134, 2159616⟩, ⟨23, 109974, 1307537⟩, ⟨18329, 138, 1443810⟩]⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 2529403 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate, FieldPrimeNode01.prime, FieldPrimeNode02.prime, FieldPrimeNode09.prime, FieldPrimeNode24.prime]

end ShielddSecurity.FieldPrimeNode33
