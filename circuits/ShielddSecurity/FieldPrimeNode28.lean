-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate
import ShielddSecurity.FieldPrimeNode01
import ShielddSecurity.FieldPrimeNode02
import ShielddSecurity.FieldPrimeNode25

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode28
open LucasCertificate

def certificate : Certificate := ⟨125527, 5, [⟨2, 62763, 125526⟩, ⟨3, 41842, 5361⟩, ⟨20921, 6, 15625⟩]⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 125527 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate, FieldPrimeNode01.prime, FieldPrimeNode02.prime, FieldPrimeNode25.prime]

end ShielddSecurity.FieldPrimeNode28
