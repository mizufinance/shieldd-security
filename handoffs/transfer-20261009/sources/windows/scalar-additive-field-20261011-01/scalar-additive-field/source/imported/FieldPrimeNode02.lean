-- GENERATED from the exact parent candidate by generate-field-certificate-tree-20261009-01.py.
import ShielddSecurity.LucasCertificate
import ShielddSecurity.FieldPrimeNode01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldPrimeNode02
open LucasCertificate

def certificate : Certificate := ⟨3, 2, [⟨2, 1, 2⟩]⟩

theorem checked : certificate.check = true := by decide +kernel

theorem prime : Nat.Prime 3 := by
  change Nat.Prime certificate.n
  apply certificate_sound certificate _ checked
  simp [certificate, FieldPrimeNode01.prime]

end ShielddSecurity.FieldPrimeNode02

set_option pp.all true in
#check @ShielddSecurity.FieldPrimeNode02.certificate
#print axioms ShielddSecurity.FieldPrimeNode02.certificate
set_option pp.all true in
#check @ShielddSecurity.FieldPrimeNode02.checked
#print axioms ShielddSecurity.FieldPrimeNode02.checked
set_option pp.all true in
#check @ShielddSecurity.FieldPrimeNode02.prime
#print axioms ShielddSecurity.FieldPrimeNode02.prime
