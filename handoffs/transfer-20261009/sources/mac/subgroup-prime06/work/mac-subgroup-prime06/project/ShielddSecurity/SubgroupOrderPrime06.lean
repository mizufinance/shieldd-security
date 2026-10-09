import ShielddSecurity.Scalar
import ShielddSecurity.SubgroupPrimeNode37

namespace ShielddSecurity.SubgroupOrderPrime06
/-- Numerical primality of the canonical campaign subgroup-order constant. -/
theorem order_prime : Nat.Prime Scalar.order := SubgroupPrimeNode37.prime
set_option pp.all true in
#check @ShielddSecurity.SubgroupOrderPrime06.order_prime
#print axioms ShielddSecurity.SubgroupOrderPrime06.order_prime
end ShielddSecurity.SubgroupOrderPrime06
