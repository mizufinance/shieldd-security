-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate
import ShielddSecurity.FieldPrimeNode01
import ShielddSecurity.FieldPrimeNode10
import ShielddSecurity.FieldPrimeNode15

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode24
open LucasCertificate

def certificate : Certificate := ⟨18329, 3, [⟨2, 9164, 18328⟩, ⟨2, 9164, 18328⟩, ⟨2, 9164, 18328⟩, ⟨29, 632, 8708⟩, ⟨79, 232, 16492⟩]⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 18329 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate, FieldPrimeNode01.prime, FieldPrimeNode10.prime, FieldPrimeNode15.prime]

end ShielddSecurity.FieldPrimeNode24
