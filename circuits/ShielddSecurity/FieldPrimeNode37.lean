-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate
import ShielddSecurity.FieldPrimeNode01
import ShielddSecurity.FieldPrimeNode36

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode37
open LucasCertificate

def certificate : Certificate := ⟨254760293, 2, [⟨2, 127380146, 254760292⟩, ⟨2, 127380146, 254760292⟩, ⟨63690073, 4, 16⟩]⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 254760293 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate, FieldPrimeNode01.prime, FieldPrimeNode36.prime]

end ShielddSecurity.FieldPrimeNode37
