import ShielddSecurity.CapturedNextLowLimb140
import ShielddSecurity.BoundedLimbComparison119
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedNextLowLimb141
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
open CapturedNextLowLimb140
variable {F : Type} [Field F]
noncomputable def prepared (base : Nat → F) (a b column : Nat) : F :=
  if column=1373 then BinaryComparison100.bit (BoundedLimbComparison119.borrow a b)
  else if column=1374 then (BoundedLimbComparison119.difference 128 a b:F) else base column
noncomputable def seeded (base : Nat → F) (a b : Nat) : Nat → F :=
  writeBits (prepared base a b) 1375 (encodeBits 128 (BoundedLimbComparison119.difference 128 a b))
theorem outside (base : Nat → F) (a b column : Nat) (bound : column<1373 ∨ 1503≤column) :
    seeded base a b column=base column := by
  unfold seeded
  rw [writeBits_preserves _ 1375 _ column (by rw [encodeBits_length];omega)]
  have h981 : column≠1373 := by omega
  have h982 : column≠1374 := by omega
  simp only [prepared,if_neg h981,if_neg h982]
theorem borrow_value (base : Nat → F) (a b : Nat) :
    seeded base a b 1373=BinaryComparison100.bit (F:=F) (BoundedLimbComparison119.borrow a b) := by
  unfold seeded
  rw [writeBits_preserves _ 1375 _ 1373 (Or.inl (by decide))]
  simp only [prepared,if_true]
theorem difference_value (base : Nat → F) (a b : Nat) :
    seeded base a b 1374=(BoundedLimbComparison119.difference 128 a b:F) := by
  unfold seeded
  rw [writeBits_preserves _ 1375 _ 1374 (Or.inl (by decide))]
  simp only [prepared,show ¬1374=1373 from by decide,if_false,if_true]
theorem range_rows (base : Nat → F) (a b : Nat) (left : a<2^128) (right : b<2^128) :
    Satisfies (seeded base a b) (columns.map booleanRow++[reconstructionRow 1374 columns]) := by
  exact writeBits_range_complete (prepared base a b) 1374 1375 128 (BoundedLimbComparison119.difference 128 a b)
    (BoundedLimbComparison119.difference_bound 128 a b left right)
    (by simp only [prepared,show ¬1374=1373 from by decide,if_false,if_true]) (Or.inl (by decide))
theorem booleans (base : Nat → F) (a b : Nat) (left : a<2^128) (right : b<2^128)
    (index : Nat) (bound : index<129) :
    Square (seeded base a b (if index=0 then 1373 else 1374+index))
      (seeded base a b (if index=0 then 1373 else 1374+index)) := by
  by_cases first : index=0
  · rw [if_pos first,borrow_value]
    exact BoundedLimbComparison119.borrow_boolean a b
  · have member : 1374+index∈columns := by
      change 1374+index∈List.range' 1375 128
      exact List.mem_range'.mpr ⟨index-1,by omega,by omega⟩
    rw [if_neg first]
    have h:=range_rows base a b left right (booleanRow (1374+index))
      (List.mem_append_left _ (List.mem_map.mpr ⟨1374+index,member,rfl⟩))
    simpa only [booleanRow,eval,Int.cast_one,one_mul,add_zero] using h
theorem reconstruction (base : Nat → F) (a b : Nat) (left : a<2^128) (right : b<2^128) :
    fieldBinary (columns.map (seeded base a b))=seeded base a b 1374 :=
  reconstruction_row_sound _ 1374 columns
    (List.mem_append_right _ (List.mem_singleton.mpr rfl)) _ (range_rows base a b left right)
theorem low_map (base : Nat → F) (a b : Nat) (cs : List Nat) (low : ∀ column∈cs,column<1373) :
    cs.map (seeded base a b)=cs.map base := by
  apply List.map_congr_left
  intro column member
  exact outside base a b column (Or.inl (low column member))
theorem balance (base : Nat → F) (a b : Nat) (left : a<2^128)
    (leftMeaning : fieldBinary (leftColumns.map base)=(a:F))
    (rightMeaning : fieldBinary (rightColumns.map base)=(b:F)) :
    fieldBinary (rightColumns.map (seeded base a b))-fieldBinary (leftColumns.map (seeded base a b))=
      seeded base a b 1374-seeded base a b 1373*(2^128:F) := by
  rw [low_map base a b rightColumns (by decide),low_map base a b leftColumns (by decide),
    leftMeaning,rightMeaning,difference_value,borrow_value]
  exact BoundedLimbComparison119.field_balance 128 a b left
theorem truth (base : Nat → F) (a b : Nat) (left : a<2^128) (right : b<2^128)
    (leftMeaning : fieldBinary (leftColumns.map base)=(a:F))
    (rightMeaning : fieldBinary (rightColumns.map base)=(b:F)) : TruthAt (seeded base a b) block.recipe 131 := by
  intro index bound hint found
  rw [hint_exact index hint found]
  by_cases bit : index<129
  · change Truth (seeded base a b) (if index<129 then _ else _)
    rw [if_pos bit]
    change Square (eval (seeded base a b) [(if index=0 then 1373 else 1374+index,1)])
      (eval (seeded base a b) [(if index=0 then 1373 else 1374+index,1)])
    simpa only [eval,Int.cast_one,one_mul,add_zero] using booleans base a b left right index bit
  · change Truth (seeded base a b) (if index<129 then _ else _)
    rw [if_neg bit]
    by_cases recon : index=129
    · rw [if_pos recon]
      change eval (seeded base a b) (weighted columns 1)=eval (seeded base a b) [(1374,1)]
      simpa only [weighted_eval,Int.cast_one,one_mul,eval,add_zero] using reconstruction base a b left right
    · rw [if_neg recon]
      change eval (seeded base a b) (weighted rightColumns 1++weighted leftColumns (-1))=
        eval (seeded base a b) [(1374,1),(1373,-(2^128))]
      calc
        _ = fieldBinary (rightColumns.map (seeded base a b))-fieldBinary (leftColumns.map (seeded base a b)) := by
          rw [eval_append,weighted_eval,weighted_eval]
          simp [sub_eq_add_neg]
        _ = seeded base a b 1374-seeded base a b 1373*(2^128:F) := balance base a b left leftMeaning rightMeaning
        _ = _ := by simp [eval];ring
variable [CharP F p]
theorem actual_complete (base : Nat → F) (a b : Nat) (left : a<2^128) (right : b<2^128)
    (leftMeaning : fieldBinary (leftColumns.map base)=(a:F))
    (rightMeaning : fieldBinary (rightColumns.map base)=(b:F)) (linked : base copy=base 0) :
    SatisfiesAt (seeded base a b) block.actual 131 := by
  apply (satisfies_iff copy 131 block _ _).mpr
  · exact truth base a b left right leftMeaning rightMeaning
  · exact (outside base a b copy (Or.inr (by decide))).trans
      (linked.trans (outside base a b 0 (Or.inl (by decide))).symm)
theorem full_complete (base : Nat → F) (a b : Nat) (left : a<2^128) (right : b<2^128)
    (leftMeaning : fieldBinary (leftColumns.map base)=(a:F))
    (rightMeaning : fieldBinary (rightColumns.map base)=(b:F)) (linked : base copy=base 0) :
    SatisfiesAt (seeded base a b) (fun index => CapturedFullRelation58.rowAt (179290+index)) 131 := by
  have done:=actual_complete base a b left right leftMeaning rightMeaning linked
  intro index before row found
  change CapturedFullRelation58.rowAt (179290+index)=some row at found
  rw [full_position index before] at found
  exact done index before row found
end ShielddSecurity.CapturedNextLowLimb141

set_option pp.all true in
#check @ShielddSecurity.CapturedNextLowLimb141.prepared
#print axioms ShielddSecurity.CapturedNextLowLimb141.prepared
set_option pp.all true in
#check @ShielddSecurity.CapturedNextLowLimb141.seeded
#print axioms ShielddSecurity.CapturedNextLowLimb141.seeded
set_option pp.all true in
#check @ShielddSecurity.CapturedNextLowLimb141.outside
#print axioms ShielddSecurity.CapturedNextLowLimb141.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedNextLowLimb141.borrow_value
#print axioms ShielddSecurity.CapturedNextLowLimb141.borrow_value
set_option pp.all true in
#check @ShielddSecurity.CapturedNextLowLimb141.difference_value
#print axioms ShielddSecurity.CapturedNextLowLimb141.difference_value
set_option pp.all true in
#check @ShielddSecurity.CapturedNextLowLimb141.range_rows
#print axioms ShielddSecurity.CapturedNextLowLimb141.range_rows
set_option pp.all true in
#check @ShielddSecurity.CapturedNextLowLimb141.booleans
#print axioms ShielddSecurity.CapturedNextLowLimb141.booleans
set_option pp.all true in
#check @ShielddSecurity.CapturedNextLowLimb141.reconstruction
#print axioms ShielddSecurity.CapturedNextLowLimb141.reconstruction
set_option pp.all true in
#check @ShielddSecurity.CapturedNextLowLimb141.low_map
#print axioms ShielddSecurity.CapturedNextLowLimb141.low_map
set_option pp.all true in
#check @ShielddSecurity.CapturedNextLowLimb141.balance
#print axioms ShielddSecurity.CapturedNextLowLimb141.balance
set_option pp.all true in
#check @ShielddSecurity.CapturedNextLowLimb141.truth
#print axioms ShielddSecurity.CapturedNextLowLimb141.truth
set_option pp.all true in
#check @ShielddSecurity.CapturedNextLowLimb141.actual_complete
#print axioms ShielddSecurity.CapturedNextLowLimb141.actual_complete
set_option pp.all true in
#check @ShielddSecurity.CapturedNextLowLimb141.full_complete
#print axioms ShielddSecurity.CapturedNextLowLimb141.full_complete
