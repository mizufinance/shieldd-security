-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate
import ShielddSecurity.FieldPrimeNode01
import ShielddSecurity.FieldPrimeNode02
import ShielddSecurity.FieldPrimeNode13

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode23
open LucasCertificate

def certificate : Certificate := ⟨10177, 7, [⟨2, 5088, 10176⟩, ⟨2, 5088, 10176⟩, ⟨2, 5088, 10176⟩, ⟨2, 5088, 10176⟩, ⟨2, 5088, 10176⟩, ⟨2, 5088, 10176⟩, ⟨3, 3392, 4773⟩, ⟨53, 192, 3616⟩]⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 10177 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate, FieldPrimeNode01.prime, FieldPrimeNode02.prime, FieldPrimeNode13.prime]

end ShielddSecurity.FieldPrimeNode23
