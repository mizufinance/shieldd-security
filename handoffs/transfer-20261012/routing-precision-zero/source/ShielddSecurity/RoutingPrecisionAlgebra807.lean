import ShielddSecurity.FieldZeroSeed125
import ShielddSecurity.RegistryNaturalSeed298
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RoutingPrecisionAlgebra807
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
attribute [local irreducible] model

theorem flag_meaning (value index : Nat) (valueBound : value<TransferCore.fieldModulus)
    (indexBound : index<TransferCore.fieldModulus) :
    FieldZeroSeed125.flag ((value:F)-(index:F))=if value=index then 1 else 0 := by
  by_cases equal : value=index
  · simp [equal,FieldZeroSeed125.flag]
  · have nonzero : (value:F)-(index:F)≠0 := by
      intro zero
      have values := congrArg representation.value (sub_eq_zero.mp zero)
      rw [RegistryNaturalSeed298.represented_nat _ valueBound,
        RegistryNaturalSeed298.represented_nat _ indexBound] at values
      exact equal values
    simp only [FieldZeroSeed125.flag,if_neg nonzero,if_neg equal]

theorem indicator_sum (value : Nat) (xs : List Nat) (distinct : xs.Nodup) :
    (xs.map (fun (index : Nat) => if value=index then (1:F) else 0)).sum=if value∈xs then 1 else 0 := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
    have fresh := (List.nodup_cons.mp distinct).1
    have remaining := (List.nodup_cons.mp distinct).2
    rw [List.map_cons,List.sum_cons,ih remaining]
    by_cases equal : value=head
    · subst value
      simp [fresh]
    · simp [equal]

theorem flag_sum (value : Nat) (valueBound : value<TransferCore.fieldModulus)
    (xs : List Nat) (distinct : xs.Nodup)
    (bounds : ∀ index∈xs,index<TransferCore.fieldModulus) :
    (xs.map (fun (index : Nat) => FieldZeroSeed125.flag ((value:F)-(index:F)))).sum=if value∈xs then 1 else 0 := by
  have rewrite : xs.map (fun (index : Nat) => FieldZeroSeed125.flag ((value:F)-(index:F)))=
      xs.map (fun (index : Nat) => if value=index then (1:F) else 0) := by
    apply List.map_congr_left
    intro index member
    exact flag_meaning value index valueBound (bounds index member)
  rw [rewrite,indicator_sum value xs distinct]

theorem full_sum (value : Nat) (bound : value≤32) :
    ((List.range 33).map (fun (index : Nat) => FieldZeroSeed125.flag ((value:F)-(index:F)))).sum=1 := by
  have fieldBound : 33<TransferCore.fieldModulus := by decide
  rw [flag_sum value (by omega) (List.range 33) List.nodup_range (by
    intro index member
    have := List.mem_range.mp member
    omega),if_pos (List.mem_range.mpr (by omega))]

def suffix (value index : Nat) : F :=
  ((List.range' (index+1) (32-index)).map (fun (item : Nat) => FieldZeroSeed125.flag ((value:F)-(item:F)))).sum

theorem suffix_value (value index : Nat) (bound : value≤32) (before : index<32) :
    suffix value index=if index<value then 1 else 0 := by
  have fieldBound : 33<TransferCore.fieldModulus := by decide
  unfold suffix
  rw [flag_sum value (by omega) _ (List.nodup_range') (by
    intro item member
    obtain ⟨offset,within,equal⟩ := List.mem_range'.mp member
    simp only [Nat.one_mul] at equal
    omega)]
  have member : value∈List.range' (index+1) (32-index) ↔ index<value := by
    constructor
    · intro member
      obtain ⟨offset,within,equal⟩ := List.mem_range'.mp member
      simp only [Nat.one_mul] at equal
      omega
    · intro after
      apply List.mem_range'.mpr
      exact ⟨value-(index+1),by omega,by omega⟩
  simp only [member]

theorem ordered_suffix (regulated unregulated index : Nat)
    (ordered : regulated≤unregulated) (bound : unregulated≤32) (before : index<32) :
    suffix regulated index*(1-suffix unregulated index)=0 := by
  rw [suffix_value regulated index (by omega) before,suffix_value unregulated index bound before]
  by_cases first : index<regulated
  · have second : index<unregulated := by omega
    simp [first,second]
  · simp [first]

theorem selected_boolean (regulated unregulated index : Nat) (flag : Bool)
    (regulatedBound : regulated≤32) (unregulatedBound : unregulated≤32) (before : index<32) :
    let selected := if flag then suffix regulated index else suffix unregulated index
    selected*selected=selected := by
  rw [suffix_value regulated index regulatedBound before,suffix_value unregulated index unregulatedBound before]
  cases flag <;> split_ifs <;> norm_num
end ShielddSecurity.RoutingPrecisionAlgebra807

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionAlgebra807.flag_meaning
#print axioms ShielddSecurity.RoutingPrecisionAlgebra807.flag_meaning

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionAlgebra807.indicator_sum
#print axioms ShielddSecurity.RoutingPrecisionAlgebra807.indicator_sum

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionAlgebra807.flag_sum
#print axioms ShielddSecurity.RoutingPrecisionAlgebra807.flag_sum

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionAlgebra807.full_sum
#print axioms ShielddSecurity.RoutingPrecisionAlgebra807.full_sum

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionAlgebra807.suffix_value
#print axioms ShielddSecurity.RoutingPrecisionAlgebra807.suffix_value

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionAlgebra807.ordered_suffix
#print axioms ShielddSecurity.RoutingPrecisionAlgebra807.ordered_suffix

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionAlgebra807.selected_boolean
#print axioms ShielddSecurity.RoutingPrecisionAlgebra807.selected_boolean
