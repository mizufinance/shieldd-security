-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate
import ShielddSecurity.FieldPrimeNode01
import ShielddSecurity.FieldPrimeNode04
import ShielddSecurity.FieldPrimeNode05
import ShielddSecurity.FieldPrimeNode19

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode27
open LucasCertificate

def certificate : Certificate := ⟨110573, 3, [⟨2, 55286, 110572⟩, ⟨2, 55286, 110572⟩, ⟨7, 15796, 68842⟩, ⟨11, 10052, 59068⟩, ⟨359, 308, 48848⟩]⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 110573 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate, FieldPrimeNode01.prime, FieldPrimeNode04.prime, FieldPrimeNode05.prime, FieldPrimeNode19.prime]

end ShielddSecurity.FieldPrimeNode27
