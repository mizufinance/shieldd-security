-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate
import ShielddSecurity.FieldPrimeNode01
import ShielddSecurity.FieldPrimeNode11
import ShielddSecurity.FieldPrimeNode29

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode35
open LucasCertificate

def certificate : Certificate := ⟨52437899, 2, [⟨2, 26218949, 52437898⟩, ⟨43, 1219486, 11758757⟩, ⟨609743, 86, 27034091⟩]⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 52437899 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate, FieldPrimeNode01.prime, FieldPrimeNode11.prime, FieldPrimeNode29.prime]

end ShielddSecurity.FieldPrimeNode35
