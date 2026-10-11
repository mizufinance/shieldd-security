import ShielddSecurity.CapturedValueComparison106
import ShielddSecurity.CapturedRegistryValueRange97
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedValueCanonical107
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
def valueLC : Linear := [(0,1),(470,(p:Int)-1),(32752,1)]
def expected (index : Nat) : Recipe :=
    if index=0 then .square valueLC valueLC else .linear [(0,1)] valueLC
noncomputable def block : Block p copy 2 where
    actual := fun index => CapturedAssertions50B0001.block.actual (165+index)
    recipe := fun index => CapturedAssertions50B0001.block.recipe (165+index)
    exact_checked := by
      intro index bound
      exact CapturedAssertions50B0001.block.exact_checked (165+index) (by omega)
theorem hint_exact (index : Nat) (bound : index<2) : block.recipe index=some (true,expected index) := by
    have cases : index=0 ∨ index=1 := by omega
    rcases cases with rfl|rfl <;> decide +kernel
theorem full_position (index : Nat) (bound : index<2) :
    CapturedFullRelation58.rowAt (178375+index)=block.actual index := by
  have sum : 178375+index=177954+(421+index) := by omega
  rw [sum,CapturedFullRelation58.assertion_position (421+index) (by omega)]
  have h12288 : 421+index<12288 := by omega
  have h4096 : 421+index<4096 := by omega
  have h2048 : 421+index<2048 := by omega
  have h1024 : 421+index<1024 := by omega
  have h512 : 421+index<512 := by omega
  change (if 421+index<12288 then _ else _) = _
  rw [if_pos h12288]
  change (if 421+index<4096 then _ else _) = _
  rw [if_pos h4096]
  change (if 421+index<2048 then _ else _) = _
  rw [if_pos h2048]
  change (if 421+index<1024 then _ else _) = _
  rw [if_pos h1024]
  change (if 421+index<512 then _ else _) = _
  rw [if_pos h512]
  change (if 421+index<256 then CapturedAssertions50B0000.block.actual (421+index)
    else CapturedAssertions50B0001.block.actual (421+index-256)) = CapturedAssertions50B0001.block.actual (165+index)
  have after : ¬421+index<256 := by omega
  have same : 421+index-256=165+index := by omega
  rw [if_neg after,same]
variable {F : Type} [Field F] [CharP F p]
theorem value_one (rho : Nat → F) (n : Nat) (bound : n<p) (zero : rho 0=1) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (bits : ∀ index<255,rho (216+index)=BinaryComparison100.bit (F:=F) (CapturedValueComparison106.bitAt n (216+index))) :
    eval rho valueLC=1 := by
  have numeric:=CapturedValueComparison106.semantic rho n bound one arithmetic bits
  have normalization : canonical p valueLC=canonical p [(0,1),(470,-1),(32752,1)] := by decide +kernel
  have normalized:=canonical_equal rho valueLC [(0,1),(470,-1),(32752,1)] normalization
  rw [normalized]
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,neg_mul,add_zero,zero,sub_eq_add_neg,add_assoc] using numeric
theorem truth (rho : Nat → F) (n : Nat) (bound : n<p) (zero : rho 0=1) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (bits : ∀ index<255,rho (216+index)=BinaryComparison100.bit (F:=F) (CapturedValueComparison106.bitAt n (216+index))) :
    TruthAt rho block.recipe 2 := by
  have value:=value_one rho n bound zero one arithmetic bits
  intro index before hint found
  have same : hint=(true,expected index) := Option.some.inj (found.symm.trans (hint_exact index before))
  subst hint
  have cases : index=0 ∨ index=1 := by omega
  rcases cases with rfl|rfl
  · change eval rho valueLC*eval rho valueLC=eval rho valueLC
    rw [value]
    ring
  · change eval rho [(0,1)]=eval rho valueLC
    simp only [eval,Int.cast_one,one_mul,add_zero,zero,value]
theorem complete (rho : Nat → F) (n : Nat) (bound : n<p) (zero : rho 0=1) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (bits : ∀ index<255,rho (216+index)=BinaryComparison100.bit (F:=F) (CapturedValueComparison106.bitAt n (216+index))) :
    SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (178375+index)) 2 := by
  have localRows:=(satisfies_iff copy 2 block rho (one.trans zero.symm)).mpr (truth rho n bound zero one arithmetic bits)
  intro index before row found
  change CapturedFullRelation58.rowAt (178375+index)=some row at found
  rw [full_position index before] at found
  exact localRows index before row found
end ShielddSecurity.CapturedValueCanonical107

set_option pp.all true in
#check @ShielddSecurity.CapturedValueCanonical107.valueLC
#print axioms ShielddSecurity.CapturedValueCanonical107.valueLC
set_option pp.all true in
#check @ShielddSecurity.CapturedValueCanonical107.expected
#print axioms ShielddSecurity.CapturedValueCanonical107.expected
set_option pp.all true in
#check @ShielddSecurity.CapturedValueCanonical107.block
#print axioms ShielddSecurity.CapturedValueCanonical107.block
set_option pp.all true in
#check @ShielddSecurity.CapturedValueCanonical107.hint_exact
#print axioms ShielddSecurity.CapturedValueCanonical107.hint_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedValueCanonical107.full_position
#print axioms ShielddSecurity.CapturedValueCanonical107.full_position
set_option pp.all true in
#check @ShielddSecurity.CapturedValueCanonical107.value_one
#print axioms ShielddSecurity.CapturedValueCanonical107.value_one
set_option pp.all true in
#check @ShielddSecurity.CapturedValueCanonical107.truth
#print axioms ShielddSecurity.CapturedValueCanonical107.truth
set_option pp.all true in
#check @ShielddSecurity.CapturedValueCanonical107.complete
#print axioms ShielddSecurity.CapturedValueCanonical107.complete
