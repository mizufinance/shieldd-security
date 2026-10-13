import ShielddSecurity.CapturedAuthorizationShared419
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationRingProduct420A
open Compiler CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
def ringRows : List Row :=
 [⟨[(10,1),(23,(p:Int)-1),(copy,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(33797,1)]⟩,
  ⟨[(10,1),(23,1),(copy,2613035198500699080012737903016384954916552590968062488514021062113153911183)],[(33796,4),(33797,1)]⟩]
theorem ring_checked : CapturedFullArithmetic52.rowAt 11058=ringRows[0]? ∧
    CapturedFullArithmetic52.rowAt 11059=ringRows[1]? := by decide +kernel

theorem ring_product (rho : Nat → F)
    (arithmetic : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 33796=rho 10*(rho 23-(49822839976625491399435002605169580882773999909559575334089637637825427273330:F)*rho copy) := by
  have sat : Satisfies rho ringRows := by
    intro row member
    simp only [ringRows,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · exact arithmetic 11058 (by decide) _ ring_checked.1
    · exact arithmetic 11059 (by decide) _ ring_checked.2
  have h := checked_product_sound rho ringRows [(10,1)]
    [(23,1),(copy,-49822839976625491399435002605169580882773999909559575334089637637825427273330)]
    [(33796,1)] [(33797,1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,one_mul,add_zero,Int.cast_neg,Int.cast_ofNat,neg_mul,sub_eq_add_neg] using h


end ShielddSecurity.AuthorizationRingProduct420A

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRingProduct420A.ringRows
#print axioms ShielddSecurity.AuthorizationRingProduct420A.ringRows

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRingProduct420A.ring_checked
#print axioms ShielddSecurity.AuthorizationRingProduct420A.ring_checked

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRingProduct420A.ring_product
#print axioms ShielddSecurity.AuthorizationRingProduct420A.ring_product
