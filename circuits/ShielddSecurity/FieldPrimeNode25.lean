-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate
import ShielddSecurity.FieldPrimeNode01
import ShielddSecurity.FieldPrimeNode03
import ShielddSecurity.FieldPrimeNode21

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode25
open LucasCertificate

def certificate : Certificate := ⟨20921, 3, [⟨2, 10460, 20920⟩, ⟨2, 10460, 20920⟩, ⟨2, 10460, 20920⟩, ⟨5, 4184, 5152⟩, ⟨523, 40, 8962⟩]⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 20921 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate, FieldPrimeNode01.prime, FieldPrimeNode03.prime, FieldPrimeNode21.prime]

end ShielddSecurity.FieldPrimeNode25
