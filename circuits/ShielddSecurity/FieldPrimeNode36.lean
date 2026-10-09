-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate
import ShielddSecurity.FieldPrimeNode01
import ShielddSecurity.FieldPrimeNode02
import ShielddSecurity.FieldPrimeNode34

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode36
open LucasCertificate

def certificate : Certificate := ⟨63690073, 7, [⟨2, 31845036, 63690072⟩, ⟨2, 31845036, 63690072⟩, ⟨2, 31845036, 63690072⟩, ⟨3, 21230024, 2527736⟩, ⟨2653753, 24, 36433797⟩]⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 63690073 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate, FieldPrimeNode01.prime, FieldPrimeNode02.prime, FieldPrimeNode34.prime]

end ShielddSecurity.FieldPrimeNode36
