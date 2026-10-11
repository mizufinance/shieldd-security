import ShielddSecurity.CapturedNextHighLimb133
import ShielddSecurity.BoundedLimbComparison119
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedNextHighLimb134
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
open CapturedNextHighLimb133
variable {F : Type} [Field F]
noncomputable def prepared (base : Nat → F) (a b column : Nat) : F :=
  if column=1242 then BinaryComparison100.bit (BoundedLimbComparison119.borrow a b)
  else if column=1243 then (BoundedLimbComparison119.difference 127 a b:F) else base column
noncomputable def seeded (base : Nat → F) (a b : Nat) : Nat → F :=
  writeBits (prepared base a b) 1244 (encodeBits 127 (BoundedLimbComparison119.difference 127 a b))
theorem outside (base : Nat → F) (a b column : Nat) (bound : column<1242 ∨ 1371≤column) :
    seeded base a b column=base column := by
  unfold seeded
  rw [writeBits_preserves _ 1244 _ column (by rw [encodeBits_length];omega)]
  have h981 : column≠1242 := by omega
  have h982 : column≠1243 := by omega
  simp only [prepared,if_neg h981,if_neg h982]
theorem borrow_value (base : Nat → F) (a b : Nat) :
    seeded base a b 1242=BinaryComparison100.bit (F:=F) (BoundedLimbComparison119.borrow a b) := by
  unfold seeded
  rw [writeBits_preserves _ 1244 _ 1242 (Or.inl (by decide))]
  simp only [prepared,if_true]
theorem difference_value (base : Nat → F) (a b : Nat) :
    seeded base a b 1243=(BoundedLimbComparison119.difference 127 a b:F) := by
  unfold seeded
  rw [writeBits_preserves _ 1244 _ 1243 (Or.inl (by decide))]
  simp only [prepared,show ¬1243=1242 from by decide,if_false,if_true]
theorem range_rows (base : Nat → F) (a b : Nat) (left : a<2^127) (right : b<2^127) :
    Satisfies (seeded base a b) (columns.map booleanRow++[reconstructionRow 1243 columns]) := by
  exact writeBits_range_complete (prepared base a b) 1243 1244 127 (BoundedLimbComparison119.difference 127 a b)
    (BoundedLimbComparison119.difference_bound 127 a b left right)
    (by simp only [prepared,show ¬1243=1242 from by decide,if_false,if_true]) (Or.inl (by decide))
theorem booleans (base : Nat → F) (a b : Nat) (left : a<2^127) (right : b<2^127)
    (index : Nat) (bound : index<128) :
    Square (seeded base a b (if index=0 then 1242 else 1243+index))
      (seeded base a b (if index=0 then 1242 else 1243+index)) := by
  by_cases first : index=0
  · rw [if_pos first,borrow_value]
    exact BoundedLimbComparison119.borrow_boolean a b
  · have member : 1243+index∈columns := by
      change 1243+index∈List.range' 1244 127
      exact List.mem_range'.mpr ⟨index-1,by omega,by omega⟩
    rw [if_neg first]
    have h:=range_rows base a b left right (booleanRow (1243+index))
      (List.mem_append_left _ (List.mem_map.mpr ⟨1243+index,member,rfl⟩))
    simpa only [booleanRow,eval,Int.cast_one,one_mul,add_zero] using h
theorem reconstruction (base : Nat → F) (a b : Nat) (left : a<2^127) (right : b<2^127) :
    fieldBinary (columns.map (seeded base a b))=seeded base a b 1243 :=
  reconstruction_row_sound _ 1243 columns
    (List.mem_append_right _ (List.mem_singleton.mpr rfl)) _ (range_rows base a b left right)
theorem low_map (base : Nat → F) (a b : Nat) (cs : List Nat) (low : ∀ column∈cs,column<1242) :
    cs.map (seeded base a b)=cs.map base := by
  apply List.map_congr_left
  intro column member
  exact outside base a b column (Or.inl (low column member))
theorem balance (base : Nat → F) (a b : Nat) (left : a<2^127)
    (leftMeaning : fieldBinary (leftColumns.map base)=(a:F))
    (rightMeaning : fieldBinary (rightColumns.map base)=(b:F)) :
    fieldBinary (rightColumns.map (seeded base a b))-fieldBinary (leftColumns.map (seeded base a b))=
      seeded base a b 1243-seeded base a b 1242*(2^127:F) := by
  rw [low_map base a b rightColumns (by decide),low_map base a b leftColumns (by decide),
    leftMeaning,rightMeaning,difference_value,borrow_value]
  exact BoundedLimbComparison119.field_balance 127 a b left
theorem truth (base : Nat → F) (a b : Nat) (left : a<2^127) (right : b<2^127)
    (leftMeaning : fieldBinary (leftColumns.map base)=(a:F))
    (rightMeaning : fieldBinary (rightColumns.map base)=(b:F)) : TruthAt (seeded base a b) block.recipe 130 := by
  intro index bound hint found
  rw [hint_exact index hint found]
  by_cases bit : index<128
  · change Truth (seeded base a b) (if index<128 then _ else _)
    rw [if_pos bit]
    change Square (eval (seeded base a b) [(if index=0 then 1242 else 1243+index,1)])
      (eval (seeded base a b) [(if index=0 then 1242 else 1243+index,1)])
    simpa only [eval,Int.cast_one,one_mul,add_zero] using booleans base a b left right index bit
  · change Truth (seeded base a b) (if index<128 then _ else _)
    rw [if_neg bit]
    by_cases recon : index=128
    · rw [if_pos recon]
      change eval (seeded base a b) (weighted columns 1)=eval (seeded base a b) [(1243,1)]
      simpa only [weighted_eval,Int.cast_one,one_mul,eval,add_zero] using reconstruction base a b left right
    · rw [if_neg recon]
      change eval (seeded base a b) (weighted rightColumns 1++weighted leftColumns (-1))=
        eval (seeded base a b) [(1243,1),(1242,-(2^127))]
      calc
        _ = fieldBinary (rightColumns.map (seeded base a b))-fieldBinary (leftColumns.map (seeded base a b)) := by
          rw [eval_append,weighted_eval,weighted_eval]
          simp [sub_eq_add_neg]
        _ = seeded base a b 1243-seeded base a b 1242*(2^127:F) := balance base a b left leftMeaning rightMeaning
        _ = _ := by simp [eval];ring
variable [CharP F p]
theorem actual_complete (base : Nat → F) (a b : Nat) (left : a<2^127) (right : b<2^127)
    (leftMeaning : fieldBinary (leftColumns.map base)=(a:F))
    (rightMeaning : fieldBinary (rightColumns.map base)=(b:F)) (linked : base copy=base 0) :
    SatisfiesAt (seeded base a b) block.actual 130 := by
  apply (satisfies_iff copy 130 block _ _).mpr
  · exact truth base a b left right leftMeaning rightMeaning
  · exact (outside base a b copy (Or.inr (by decide))).trans
      (linked.trans (outside base a b 0 (Or.inl (by decide))).symm)
theorem full_complete (base : Nat → F) (a b : Nat) (left : a<2^127) (right : b<2^127)
    (leftMeaning : fieldBinary (leftColumns.map base)=(a:F))
    (rightMeaning : fieldBinary (rightColumns.map base)=(b:F)) (linked : base copy=base 0) :
    SatisfiesAt (seeded base a b) (fun index => CapturedFullRelation58.rowAt (179157+index)) 130 := by
  have done:=actual_complete base a b left right leftMeaning rightMeaning linked
  intro index before row found
  change CapturedFullRelation58.rowAt (179157+index)=some row at found
  rw [full_position index before] at found
  exact done index before row found
end ShielddSecurity.CapturedNextHighLimb134
