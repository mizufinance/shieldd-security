import ShielddSecurity.CapturedAssertions50B0000
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedEpochRange60
open CompilerAssertionBlock51 CompilerArithmeticTransport41
noncomputable def columns : List Nat := List.range' 49 64
noncomputable def expected (index : Nat) : Recipe :=
  if index<64 then .square [(49+index,1)] [(49+index,1)]
  else .linear (weighted columns 1) [(34,1)]
def sameRecipe : Recipe → Recipe → Bool
  | .linear a b,.linear c d | .square a b,.square c d => decide (a=c ∧ b=d)
  | _,_ => false
theorem sameRecipe_sound (left right : Recipe) (checked : sameRecipe left right=true) : left=right := by
  cases left <;> cases right <;> simp only [sameRecipe,decide_eq_true_eq,Bool.false_eq_true] at checked
  all_goals first
    | contradiction
    | rcases checked with ⟨rfl,rfl⟩;rfl
noncomputable def block : Block p copy 65 where
  actual := fun index => CapturedAssertions50B0000.block.actual (25+index)
  recipe := fun index => CapturedAssertions50B0000.block.recipe (25+index)
  exact_checked := by
    intro index bound
    exact CapturedAssertions50B0000.block.exact_checked (25+index) (by omega)
noncomputable def productionCheck : Bool :=
  (List.range 65).all (fun index => match block.recipe index with
    | some hint => sameRecipe hint.2 (expected index)
    | none => false)
theorem production_checked : productionCheck=true := by decide +kernel
theorem recipes_exact (index : Nat) (bound : index<65) (hint : Bool × Recipe)
    (found : block.recipe index=some hint) : hint.2=expected index := by
  have checked:=List.all_eq_true.mp production_checked index (List.mem_range.mpr bound)
  rw [found] at checked
  exact sameRecipe_sound hint.2 (expected index) checked
variable {F : Type} [Field F]
theorem truth_iff (rho : Nat → F) : TruthAt rho block.recipe 65 ↔
    (∀ index<64,Square (rho (49+index)) (rho (49+index))) ∧
    fieldBinary (columns.map rho)=rho 34 := by
  constructor
  · intro truth
    constructor
    · intro index bound
      obtain ⟨row,hint,_,found,_⟩:=block.exact_checked index (by omega)
      have value:=truth index (by omega) hint found
      rw [recipes_exact index (by omega) hint found] at value
      change Truth rho (if index<64 then .square [(49+index,1)] [(49+index,1)]
        else .linear (weighted columns 1) [(34,1)]) at value
      rw [if_pos bound] at value
      change Square (eval rho [(49+index,1)]) (eval rho [(49+index,1)]) at value
      simpa only [eval,Int.cast_one,one_mul,add_zero] using value
    · obtain ⟨row,hint,_,found,_⟩:=block.exact_checked 64 (by decide)
      have value:=truth 64 (by decide) hint found
      rw [recipes_exact 64 (by decide) hint found] at value
      change eval rho (weighted columns 1)=eval rho [(34,1)] at value
      simpa only [weighted_eval,Int.cast_one,one_mul,eval,add_zero] using value
  · rintro ⟨bits,reconstruction⟩ index bound hint found
    rw [recipes_exact index bound hint found]
    by_cases before : index<64
    · change Truth rho (if index<64 then .square [(49+index,1)] [(49+index,1)]
        else .linear (weighted columns 1) [(34,1)])
      rw [if_pos before]
      change Square (eval rho [(49+index,1)]) (eval rho [(49+index,1)])
      simpa only [eval,Int.cast_one,one_mul,add_zero] using bits index before
    · have last : index=64 := by omega
      subst index
      change eval rho (weighted columns 1)=eval rho [(34,1)]
      simpa only [weighted_eval,Int.cast_one,one_mul,eval,add_zero] using reconstruction

theorem meaning_sound (rho : Nat → F) (truth : TruthAt rho block.recipe 65) :
    ∃ n : Nat,n<2^64 ∧ (n : F)=rho 34 := by
  have parts:=(truth_iff rho).mp truth
  have bits : ∀ x∈columns.map rho,Square x x := by
    intro x member
    obtain ⟨column,present,rfl⟩:=List.mem_map.mp member
    change column∈List.range' 49 64 at present
    obtain ⟨offset,offsetBound,offsetSame⟩:=List.mem_range'.mp present
    simp only [one_mul] at offsetSame
    have bounds : 49≤column ∧ column<49+64 := by omega
    have index : column-49<64 := by omega
    have same : 49+(column-49)=column := by omega
    simpa only [same] using parts.1 (column-49) index
  have h:=range_sound (columns.map rho) (rho 34) bits parts.2
  simpa only [columns,List.length_map,List.length_range'] using h
noncomputable def completed (base : Nat → F) (n : Nat) : Nat → F :=
  writeBits base 49 (encodeBits 64 n)
theorem completed_truth (base : Nat → F) (n : Nat) (bound : n<2^64)
    (meaning : base 34=(n : F)) : TruthAt (completed base n) block.recipe 65 := by
  have standard:=writeBits_range_complete base 34 49 64 n bound meaning (by decide)
  apply (truth_iff (completed base n)).mpr
  constructor
  · intro index before
    have member : 49+index∈columns :=
      List.mem_range'.mpr ⟨index,before,by simp only [one_mul]⟩
    have h:=standard (booleanRow (49+index))
      (List.mem_append_left _ (List.mem_map.mpr ⟨49+index,member,rfl⟩))
    simpa only [booleanRow,eval,Int.cast_one,one_mul,add_zero] using h
  · exact reconstruction_row_sound _ 34 columns
      (List.mem_append_right _ (List.mem_singleton.mpr rfl)) (completed base n) standard

theorem completed_outside (base : Nat → F) (n column : Nat)
    (outside : column<49 ∨ 113≤column) : completed base n column=base column :=
  writeBits_preserves base 49 (encodeBits 64 n) column (by simpa only [encodeBits_length] using outside)
theorem completed_fixed (base : Nat → F) (n : Nat) :
    completed base n 0=base 0 ∧ completed base n 1=base 1 ∧ completed base n 2=base 2 ∧
    completed base n copy=base copy ∧ completed base n 34=base 34 :=
  ⟨completed_outside base n 0 (by decide),completed_outside base n 1 (by decide),
    completed_outside base n 2 (by decide),completed_outside base n copy (by decide),
    completed_outside base n 34 (by decide)⟩
variable [CharP F p]
theorem actual_sound (rho : Nat → F) (linked : rho copy=rho 0)
    (satisfied : SatisfiesAt rho block.actual 65) : ∃ n : Nat,n<2^64 ∧ (n : F)=rho 34 :=
  meaning_sound rho ((CompilerAssertionBlock51.satisfies_iff copy 65 block rho linked).mp satisfied)
theorem actual_complete (base : Nat → F) (n : Nat) (bound : n<2^64)
    (meaning : base 34=(n : F)) (linked : base copy=base 0) :
    SatisfiesAt (completed base n) block.actual 65 := by
  apply (CompilerAssertionBlock51.satisfies_iff copy 65 block (completed base n) _).mpr
  · exact completed_truth base n bound meaning
  · exact (completed_fixed base n).2.2.2.1.trans (linked.trans (completed_fixed base n).1.symm)
def captureIndex (index : Nat) : Nat := 177979+index
theorem capture_position (index : Nat) (bound : index<65) : captureIndex index<178044 := by
  change 177979+index<178044
  omega
end ShielddSecurity.CapturedEpochRange60

set_option pp.all true in
#check @ShielddSecurity.CapturedEpochRange60.columns
#print axioms ShielddSecurity.CapturedEpochRange60.columns
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochRange60.expected
#print axioms ShielddSecurity.CapturedEpochRange60.expected
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochRange60.sameRecipe
#print axioms ShielddSecurity.CapturedEpochRange60.sameRecipe
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochRange60.sameRecipe_sound
#print axioms ShielddSecurity.CapturedEpochRange60.sameRecipe_sound
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochRange60.block
#print axioms ShielddSecurity.CapturedEpochRange60.block
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochRange60.productionCheck
#print axioms ShielddSecurity.CapturedEpochRange60.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochRange60.production_checked
#print axioms ShielddSecurity.CapturedEpochRange60.production_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochRange60.recipes_exact
#print axioms ShielddSecurity.CapturedEpochRange60.recipes_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochRange60.truth_iff
#print axioms ShielddSecurity.CapturedEpochRange60.truth_iff
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochRange60.meaning_sound
#print axioms ShielddSecurity.CapturedEpochRange60.meaning_sound
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochRange60.completed
#print axioms ShielddSecurity.CapturedEpochRange60.completed
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochRange60.completed_truth
#print axioms ShielddSecurity.CapturedEpochRange60.completed_truth
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochRange60.completed_outside
#print axioms ShielddSecurity.CapturedEpochRange60.completed_outside
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochRange60.completed_fixed
#print axioms ShielddSecurity.CapturedEpochRange60.completed_fixed
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochRange60.actual_sound
#print axioms ShielddSecurity.CapturedEpochRange60.actual_sound
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochRange60.actual_complete
#print axioms ShielddSecurity.CapturedEpochRange60.actual_complete
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochRange60.captureIndex
#print axioms ShielddSecurity.CapturedEpochRange60.captureIndex
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochRange60.capture_position
#print axioms ShielddSecurity.CapturedEpochRange60.capture_position
