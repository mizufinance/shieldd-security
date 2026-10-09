-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate
import ShielddSecurity.FieldPrimeNode01
import ShielddSecurity.FieldPrimeNode04
import ShielddSecurity.FieldPrimeNode17
import ShielddSecurity.FieldPrimeNode20

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode29
open LucasCertificate

def certificate : Certificate := ⟨609743, 5, [⟨2, 304871, 609742⟩, ⟨7, 87106, 207533⟩, ⟨97, 6286, 544069⟩, ⟨449, 1358, 475632⟩]⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 609743 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate, FieldPrimeNode01.prime, FieldPrimeNode04.prime, FieldPrimeNode17.prime, FieldPrimeNode20.prime]

end ShielddSecurity.FieldPrimeNode29
