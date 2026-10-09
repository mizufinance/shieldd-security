-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate
import ShielddSecurity.FieldPrimeNode01
import ShielddSecurity.FieldPrimeNode03

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode05
open LucasCertificate

def certificate : Certificate := ⟨11, 2, [⟨2, 5, 10⟩, ⟨5, 2, 4⟩]⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 11 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate, FieldPrimeNode01.prime, FieldPrimeNode03.prime]

end ShielddSecurity.FieldPrimeNode05
