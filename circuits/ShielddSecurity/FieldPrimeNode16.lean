-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate
import ShielddSecurity.FieldPrimeNode01
import ShielddSecurity.FieldPrimeNode05

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode16
open LucasCertificate

def certificate : Certificate := ⟨89, 3, [⟨2, 44, 88⟩, ⟨2, 44, 88⟩, ⟨2, 44, 88⟩, ⟨11, 8, 64⟩]⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 89 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate, FieldPrimeNode01.prime, FieldPrimeNode05.prime]

end ShielddSecurity.FieldPrimeNode16
