-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate
import ShielddSecurity.FieldPrimeNode01
import ShielddSecurity.FieldPrimeNode05
import ShielddSecurity.FieldPrimeNode14

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode22
open LucasCertificate

def certificate : Certificate := ⟨1607, 5, [⟨2, 803, 1606⟩, ⟨11, 146, 1522⟩, ⟨73, 22, 286⟩]⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 1607 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate, FieldPrimeNode01.prime, FieldPrimeNode05.prime, FieldPrimeNode14.prime]

end ShielddSecurity.FieldPrimeNode22
