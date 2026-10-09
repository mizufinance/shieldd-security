import ShielddSecurity.Scalar
import ShielddSecurity.SubgroupPrimeNode37

namespace ShielddSecurity.SubgroupOrderPrime06
/-- Numerical primality of the canonical campaign subgroup-order constant. -/
theorem order_prime : Nat.Prime Scalar.order := SubgroupPrimeNode37.prime

set_option pp.all true in
#check @order_prime
#print axioms order_prime
end ShielddSecurity.SubgroupOrderPrime06
