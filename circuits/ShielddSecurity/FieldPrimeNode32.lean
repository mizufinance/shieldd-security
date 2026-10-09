-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate
import ShielddSecurity.FieldPrimeNode01
import ShielddSecurity.FieldPrimeNode02
import ShielddSecurity.FieldPrimeNode04
import ShielddSecurity.FieldPrimeNode15

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode32
open LucasCertificate

def certificate : Certificate := ⟨2508409, 11, [⟨2, 1254204, 2508408⟩, ⟨2, 1254204, 2508408⟩, ⟨2, 1254204, 2508408⟩, ⟨3, 836136, 875787⟩, ⟨3, 836136, 875787⟩, ⟨3, 836136, 875787⟩, ⟨3, 836136, 875787⟩, ⟨7, 358344, 1491919⟩, ⟨7, 358344, 1491919⟩, ⟨79, 31752, 2251273⟩]⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 2508409 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate, FieldPrimeNode01.prime, FieldPrimeNode02.prime, FieldPrimeNode04.prime, FieldPrimeNode15.prime]

end ShielddSecurity.FieldPrimeNode32
