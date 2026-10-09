-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate
import ShielddSecurity.FieldPrimeNode01
import ShielddSecurity.FieldPrimeNode02
import ShielddSecurity.FieldPrimeNode12
import ShielddSecurity.FieldPrimeNode22

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode31
open LucasCertificate

def certificate : Certificate := ⟨906349, 2, [⟨2, 453174, 906348⟩, ⟨2, 453174, 906348⟩, ⟨3, 302116, 161246⟩, ⟨47, 19284, 69344⟩, ⟨1607, 564, 210417⟩]⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 906349 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate, FieldPrimeNode01.prime, FieldPrimeNode02.prime, FieldPrimeNode12.prime, FieldPrimeNode22.prime]

end ShielddSecurity.FieldPrimeNode31
