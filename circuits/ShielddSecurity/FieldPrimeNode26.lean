-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate
import ShielddSecurity.FieldPrimeNode01
import ShielddSecurity.FieldPrimeNode02
import ShielddSecurity.FieldPrimeNode06
import ShielddSecurity.FieldPrimeNode07

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode26
open LucasCertificate

def certificate : Certificate := ⟨47737, 5, [⟨2, 23868, 47736⟩, ⟨2, 23868, 47736⟩, ⟨2, 23868, 47736⟩, ⟨3, 15912, 42905⟩, ⟨3, 15912, 42905⟩, ⟨3, 15912, 42905⟩, ⟨13, 3672, 26006⟩, ⟨17, 2808, 23688⟩]⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 47737 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate, FieldPrimeNode01.prime, FieldPrimeNode02.prime, FieldPrimeNode06.prime, FieldPrimeNode07.prime]

end ShielddSecurity.FieldPrimeNode26
