import ShielddSecurity.PoseidonNatural192
import ShielddSecurity.CanonicalWord215
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CanonicalRepresentation219
open PoseidonNatural192
variable {F : Type} [Field F] [CharP F TransferCore.fieldModulus]
theorem bounded_cast_injective (n m : Nat) (hn : n<TransferCore.fieldModulus)
 (hm : m<TransferCore.fieldModulus) (equality : (n:F)=(m:F)) : n=m := by
 have modular := (CharP.cast_eq_iff_mod_eq (R:=F) (p:=TransferCore.fieldModulus)).mp equality
 rw [Nat.mod_eq_of_lt hn,Nat.mod_eq_of_lt hm] at modular
 exact modular
theorem natural_value (representation : CanonicalRepresentation F) (n : Nat)
 (bound : n<TransferCore.fieldModulus) : representation.value (n:F)=n :=
 bounded_cast_injective _ n (representation.bounded _) bound (representation.cast_value _)
theorem field_value (representation : CanonicalRepresentation F) (x : F) (n : Nat)
 (bound : n<TransferCore.fieldModulus) (meaning : (n:F)=x) : representation.value x=n :=
 bounded_cast_injective _ n (representation.bounded x) bound ((representation.cast_value x).trans meaning.symm)
omit [CharP F TransferCore.fieldModulus] in
theorem value_injective (representation : CanonicalRepresentation F) (x y : F)
 (equality : representation.value x=representation.value y) : x=y := by
 calc x=(representation.value x:F) := (representation.cast_value x).symm
      _=(representation.value y:F) := congrArg (fun n : Nat => (n:F)) equality
      _=y := representation.cast_value y
theorem hash_value (small : Poseidon.Parameters F 3) (wide : Poseidon.Parameters F 6)
 (representation : CanonicalRepresentation F) (domain : TransferSem.Domain) (inputs : List Nat)
 (n : Nat) (bound : n<TransferCore.fieldModulus)
 (meaning : (n:F)=Poseidon.hash small wide (TransferSem.domainCode domain) (inputs.map fun x : Nat => (x:F))) :
 hash small wide representation domain inputs=n :=
 field_value representation _ n bound meaning
end ShielddSecurity.CanonicalRepresentation219

set_option pp.all true in
#check @ShielddSecurity.CanonicalRepresentation219.bounded_cast_injective
#print axioms ShielddSecurity.CanonicalRepresentation219.bounded_cast_injective
set_option pp.all true in
#check @ShielddSecurity.CanonicalRepresentation219.natural_value
#print axioms ShielddSecurity.CanonicalRepresentation219.natural_value
set_option pp.all true in
#check @ShielddSecurity.CanonicalRepresentation219.field_value
#print axioms ShielddSecurity.CanonicalRepresentation219.field_value
set_option pp.all true in
#check @ShielddSecurity.CanonicalRepresentation219.value_injective
#print axioms ShielddSecurity.CanonicalRepresentation219.value_injective
set_option pp.all true in
#check @ShielddSecurity.CanonicalRepresentation219.hash_value
#print axioms ShielddSecurity.CanonicalRepresentation219.hash_value
