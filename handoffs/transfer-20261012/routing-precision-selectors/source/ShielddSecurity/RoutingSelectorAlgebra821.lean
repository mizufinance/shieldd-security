import ShielddSecurity.RoutingPrecisionAlgebra807
import ShielddSecurity.MapArithmeticAdapter704
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RoutingSelectorAlgebra821
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model

def flags (start : Nat) (indices : List Nat) : Linear := indices.map (fun i => (start+2*i,1))
def suffix (start index : Nat) : Linear := flags start (List.range' (index+1) (32-index))

theorem eval_flags (rho : Nat → F) (value start : Nat) (indices : List Nat)
    (values : ∀ i∈indices,rho (start+2*i)=FieldZeroSeed125.flag ((value:F)-(i:F))) :
    eval rho (flags start indices)=
      (indices.map (fun (i : Nat) => FieldZeroSeed125.flag ((value:F)-(i:F)))).sum := by
  induction indices with
  | nil => rfl
  | cons head tail ih =>
    have first := values head (by simp)
    have remaining : ∀ i∈tail,rho (start+2*i)=FieldZeroSeed125.flag ((value:F)-(i:F)) := by
      intro i member
      exact values i (List.mem_cons_of_mem head member)
    simpa only [flags,List.map_cons,eval,Int.cast_one,one_mul,List.sum_cons,first] using
      congrArg (fun x => FieldZeroSeed125.flag ((value:F)-(head:F))+x) (ih remaining)

theorem full_sum (rho : Nat → F) (value start : Nat) (bound : value≤32)
    (values : ∀ i<33,rho (start+2*i)=FieldZeroSeed125.flag ((value:F)-(i:F))) :
    eval rho (flags start (List.range 33))=1 := by
  rw [eval_flags rho value start _ (by intro i member;exact values i (List.mem_range.mp member))]
  exact RoutingPrecisionAlgebra807.full_sum value bound

theorem suffix_value (rho : Nat → F) (value start index : Nat)
    (values : ∀ i<33,rho (start+2*i)=FieldZeroSeed125.flag ((value:F)-(i:F))) :
    eval rho (suffix start index)=RoutingPrecisionAlgebra807.suffix value index := by
  apply eval_flags
  intro i member
  obtain ⟨offset,before,equal⟩ := List.mem_range'.mp member
  simp only [Nat.one_mul] at equal
  exact values i (by omega)

theorem selection (regulated unregulated flag : F) (regulatedBoolean : regulated*regulated=regulated)
    (unregulatedBoolean : unregulated*unregulated=unregulated) (flagBoolean : flag=0 ∨ flag=1) :
    let selected := unregulated+flag*(regulated-unregulated)
    selected*selected=selected := by
  rcases flagBoolean with rfl|rfl
  · simpa using unregulatedBoolean
  · dsimp only
    convert regulatedBoolean using 1 <;> ring
end ShielddSecurity.RoutingSelectorAlgebra821

set_option pp.all true in
#check @ShielddSecurity.RoutingSelectorAlgebra821.eval_flags
#print axioms ShielddSecurity.RoutingSelectorAlgebra821.eval_flags
set_option pp.all true in
#check @ShielddSecurity.RoutingSelectorAlgebra821.full_sum
#print axioms ShielddSecurity.RoutingSelectorAlgebra821.full_sum
set_option pp.all true in
#check @ShielddSecurity.RoutingSelectorAlgebra821.suffix_value
#print axioms ShielddSecurity.RoutingSelectorAlgebra821.suffix_value
set_option pp.all true in
#check @ShielddSecurity.RoutingSelectorAlgebra821.selection
#print axioms ShielddSecurity.RoutingSelectorAlgebra821.selection
