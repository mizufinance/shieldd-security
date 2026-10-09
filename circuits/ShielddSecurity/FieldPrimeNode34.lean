-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate
import ShielddSecurity.FieldPrimeNode01
import ShielddSecurity.FieldPrimeNode02
import ShielddSecurity.FieldPrimeNode27

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode34
open LucasCertificate

def certificate : Certificate := ⟨2653753, 5, [⟨2, 1326876, 2653752⟩, ⟨2, 1326876, 2653752⟩, ⟨2, 1326876, 2653752⟩, ⟨3, 884584, 2076727⟩, ⟨110573, 24, 401777⟩]⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 2653753 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate, FieldPrimeNode01.prime, FieldPrimeNode02.prime, FieldPrimeNode27.prime]

end ShielddSecurity.FieldPrimeNode34
