import ShielddSecurity.CanonicalFp206
import ShielddSecurity.FieldPrimeNode38
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.ConcreteRepresentation274
instance primeFact : Fact (Nat.Prime CanonicalFp206.p) := ⟨FieldPrimeNode38.prime⟩
abbrev F := CanonicalFp206.Fp
def representation : PoseidonNatural192.CanonicalRepresentation F := CanonicalFp206.representation
theorem bounded (x : F) : representation.value x<TransferCore.fieldModulus := representation.bounded x
theorem cast_value (x : F) : (representation.value x:F)=x := representation.cast_value x
theorem natural_value (n : Nat) (bound : n<TransferCore.fieldModulus) : representation.value (n:F)=n :=
 CanonicalFp206.natural_value n bound
end ShielddSecurity.ConcreteRepresentation274

set_option pp.all true in
#check @ShielddSecurity.ConcreteRepresentation274.primeFact
#print axioms ShielddSecurity.ConcreteRepresentation274.primeFact
set_option pp.all true in
#check @ShielddSecurity.ConcreteRepresentation274.F
#print axioms ShielddSecurity.ConcreteRepresentation274.F
set_option pp.all true in
#check @ShielddSecurity.ConcreteRepresentation274.representation
#print axioms ShielddSecurity.ConcreteRepresentation274.representation
set_option pp.all true in
#check @ShielddSecurity.ConcreteRepresentation274.bounded
#print axioms ShielddSecurity.ConcreteRepresentation274.bounded
set_option pp.all true in
#check @ShielddSecurity.ConcreteRepresentation274.cast_value
#print axioms ShielddSecurity.ConcreteRepresentation274.cast_value
set_option pp.all true in
#check @ShielddSecurity.ConcreteRepresentation274.natural_value
#print axioms ShielddSecurity.ConcreteRepresentation274.natural_value
