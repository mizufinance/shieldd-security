import ShielddSecurity.LucasCertificate

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.FieldCertificateSmallPilot01
open LucasCertificate

def node3 : Certificate := ⟨3, 2, [⟨2, 1, 2⟩]⟩
theorem node3_checked : node3.check = true := by decide +kernel
theorem node3_prime : Nat.Prime node3.n := by
  apply certificate_sound node3 _ node3_checked
  intro entry member
  simp only [node3, List.mem_cons, List.not_mem_nil, or_false] at member
  subst entry
  exact Nat.prime_two

def badFactor : Certificate := ⟨3, 2, [⟨3, 1, 2⟩]⟩
def badResidue : Certificate := ⟨3, 2, [⟨2, 1, 1⟩]⟩
def badBase : Certificate := ⟨3, 1, [⟨2, 1, 2⟩]⟩
theorem bad_factor_rejected : badFactor.check = false := by decide +kernel
theorem bad_residue_rejected : badResidue.check = false := by decide +kernel
theorem bad_base_rejected : badBase.check = false := by decide +kernel


set_option pp.all true in
#check @node3_checked
#print axioms node3_checked

set_option pp.all true in
#check @node3_prime
#print axioms node3_prime

set_option pp.all true in
#check @bad_factor_rejected
#print axioms bad_factor_rejected

set_option pp.all true in
#check @bad_residue_rejected
#print axioms bad_residue_rejected

set_option pp.all true in
#check @bad_base_rejected
#print axioms bad_base_rejected
end ShielddSecurity.FieldCertificateSmallPilot01
