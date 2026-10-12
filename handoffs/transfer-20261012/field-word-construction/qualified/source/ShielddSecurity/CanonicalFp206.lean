import Mathlib.Algebra.Field.ZMod
import ShielddSecurity.PoseidonNatural192
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CanonicalFp206
def p : Nat := TransferCore.fieldModulus
abbrev Fp := ZMod p
variable [Fact (Nat.Prime p)]
def representation : PoseidonNatural192.CanonicalRepresentation Fp where
 value:=ZMod.val
 bounded:=fun x => ZMod.val_lt x
 cast_value:=fun x => ZMod.natCast_zmod_val x
theorem bounded (x : Fp) : representation.value x<TransferCore.fieldModulus :=
 representation.bounded x
theorem cast_value (x : Fp) : (representation.value x:Fp)=x :=
 representation.cast_value x
theorem natural_value (n : Nat) (bound : n<p) : representation.value (n:Fp)=n :=
 ZMod.val_natCast_of_lt bound
end ShielddSecurity.CanonicalFp206

set_option pp.all true in
#check @ShielddSecurity.CanonicalFp206.p
#print axioms ShielddSecurity.CanonicalFp206.p
set_option pp.all true in
#check @ShielddSecurity.CanonicalFp206.Fp
#print axioms ShielddSecurity.CanonicalFp206.Fp
set_option pp.all true in
#check @ShielddSecurity.CanonicalFp206.representation
#print axioms ShielddSecurity.CanonicalFp206.representation
set_option pp.all true in
#check @ShielddSecurity.CanonicalFp206.bounded
#print axioms ShielddSecurity.CanonicalFp206.bounded
set_option pp.all true in
#check @ShielddSecurity.CanonicalFp206.cast_value
#print axioms ShielddSecurity.CanonicalFp206.cast_value
set_option pp.all true in
#check @ShielddSecurity.CanonicalFp206.natural_value
#print axioms ShielddSecurity.CanonicalFp206.natural_value
