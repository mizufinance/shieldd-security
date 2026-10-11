import ShielddSecurity.CapturedRegistryHighLimb120
import ShielddSecurity.BoundedLimbComparison119
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistryHighLimb121
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
open CapturedRegistryHighLimb120
variable {F : Type} [Field F]
noncomputable def prepared (base : Nat → F) (a b column : Nat) : F :=
  if column=981 then BinaryComparison100.bit (BoundedLimbComparison119.borrow a b)
  else if column=982 then (BoundedLimbComparison119.difference 127 a b:F) else base column
noncomputable def seeded (base : Nat → F) (a b : Nat) : Nat → F :=
  writeBits (prepared base a b) 983 (encodeBits 127 (BoundedLimbComparison119.difference 127 a b))
theorem outside (base : Nat → F) (a b column : Nat) (bound : column<981 ∨ 1110≤column) :
    seeded base a b column=base column := by
  unfold seeded
  rw [writeBits_preserves _ 983 _ column (by rw [encodeBits_length];omega)]
  have h981 : column≠981 := by omega
  have h982 : column≠982 := by omega
  simp only [prepared,if_neg h981,if_neg h982]
theorem borrow_value (base : Nat → F) (a b : Nat) :
    seeded base a b 981=BinaryComparison100.bit (F:=F) (BoundedLimbComparison119.borrow a b) := by
  unfold seeded
  rw [writeBits_preserves _ 983 _ 981 (Or.inl (by decide))]
  simp only [prepared,if_true]
theorem difference_value (base : Nat → F) (a b : Nat) :
    seeded base a b 982=(BoundedLimbComparison119.difference 127 a b:F) := by
  unfold seeded
  rw [writeBits_preserves _ 983 _ 982 (Or.inl (by decide))]
  simp only [prepared,show ¬982=981 from by decide,if_false,if_true]
theorem range_rows (base : Nat → F) (a b : Nat) (left : a<2^127) (right : b<2^127) :
    Satisfies (seeded base a b) (columns.map booleanRow++[reconstructionRow 982 columns]) := by
  exact writeBits_range_complete (prepared base a b) 982 983 127 (BoundedLimbComparison119.difference 127 a b)
    (BoundedLimbComparison119.difference_bound 127 a b left right)
    (by simp only [prepared,show ¬982=981 from by decide,if_false,if_true]) (Or.inl (by decide))
theorem booleans (base : Nat → F) (a b : Nat) (left : a<2^127) (right : b<2^127)
    (index : Nat) (bound : index<128) :
    Square (seeded base a b (if index=0 then 981 else 982+index))
      (seeded base a b (if index=0 then 981 else 982+index)) := by
  by_cases first : index=0
  · rw [if_pos first,borrow_value]
    exact BoundedLimbComparison119.borrow_boolean a b
  · have member : 982+index∈columns := by
      change 982+index∈List.range' 983 127
      exact List.mem_range'.mpr ⟨index-1,by omega,by omega⟩
    rw [if_neg first]
    have h:=range_rows base a b left right (booleanRow (982+index))
      (List.mem_append_left _ (List.mem_map.mpr ⟨982+index,member,rfl⟩))
    simpa only [booleanRow,eval,Int.cast_one,one_mul,add_zero] using h
theorem reconstruction (base : Nat → F) (a b : Nat) (left : a<2^127) (right : b<2^127) :
    fieldBinary (columns.map (seeded base a b))=seeded base a b 982 :=
  reconstruction_row_sound _ 982 columns
    (List.mem_append_right _ (List.mem_singleton.mpr rfl)) _ (range_rows base a b left right)
theorem low_map (base : Nat → F) (a b : Nat) (cs : List Nat) (low : ∀ column∈cs,column<981) :
    cs.map (seeded base a b)=cs.map base := by
  apply List.map_congr_left
  intro column member
  exact outside base a b column (Or.inl (low column member))
theorem balance (base : Nat → F) (a b : Nat) (left : a<2^127)
    (leftMeaning : fieldBinary (leftColumns.map base)=(a:F))
    (rightMeaning : fieldBinary (rightColumns.map base)=(b:F)) :
    fieldBinary (rightColumns.map (seeded base a b))-fieldBinary (leftColumns.map (seeded base a b))=
      seeded base a b 982-seeded base a b 981*(2^127:F) := by
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
    change Square (eval (seeded base a b) [(if index=0 then 981 else 982+index,1)])
      (eval (seeded base a b) [(if index=0 then 981 else 982+index,1)])
    simpa only [eval,Int.cast_one,one_mul,add_zero] using booleans base a b left right index bit
  · change Truth (seeded base a b) (if index<128 then _ else _)
    rw [if_neg bit]
    by_cases recon : index=128
    · rw [if_pos recon]
      change eval (seeded base a b) (weighted columns 1)=eval (seeded base a b) [(982,1)]
      simpa only [weighted_eval,Int.cast_one,one_mul,eval,add_zero] using reconstruction base a b left right
    · rw [if_neg recon]
      change eval (seeded base a b) (weighted rightColumns 1++weighted leftColumns (-1))=
        eval (seeded base a b) [(982,1),(981,-(2^127))]
      calc
        _ = fieldBinary (rightColumns.map (seeded base a b))-fieldBinary (leftColumns.map (seeded base a b)) := by
          rw [eval_append,weighted_eval,weighted_eval]
          simp [sub_eq_add_neg]
        _ = seeded base a b 982-seeded base a b 981*(2^127:F) := balance base a b left leftMeaning rightMeaning
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
    SatisfiesAt (seeded base a b) (fun index => CapturedFullRelation58.rowAt (178893+index)) 130 := by
  have done:=actual_complete base a b left right leftMeaning rightMeaning linked
  intro index before row found
  change CapturedFullRelation58.rowAt (178893+index)=some row at found
  rw [full_position index before] at found
  exact done index before row found
end ShielddSecurity.CapturedRegistryHighLimb121

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryHighLimb121.prepared
#print axioms ShielddSecurity.CapturedRegistryHighLimb121.prepared
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryHighLimb121.seeded
#print axioms ShielddSecurity.CapturedRegistryHighLimb121.seeded
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryHighLimb121.outside
#print axioms ShielddSecurity.CapturedRegistryHighLimb121.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryHighLimb121.borrow_value
#print axioms ShielddSecurity.CapturedRegistryHighLimb121.borrow_value
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryHighLimb121.difference_value
#print axioms ShielddSecurity.CapturedRegistryHighLimb121.difference_value
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryHighLimb121.range_rows
#print axioms ShielddSecurity.CapturedRegistryHighLimb121.range_rows
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryHighLimb121.booleans
#print axioms ShielddSecurity.CapturedRegistryHighLimb121.booleans
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryHighLimb121.reconstruction
#print axioms ShielddSecurity.CapturedRegistryHighLimb121.reconstruction
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryHighLimb121.low_map
#print axioms ShielddSecurity.CapturedRegistryHighLimb121.low_map
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryHighLimb121.balance
#print axioms ShielddSecurity.CapturedRegistryHighLimb121.balance
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryHighLimb121.truth
#print axioms ShielddSecurity.CapturedRegistryHighLimb121.truth
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryHighLimb121.actual_complete
#print axioms ShielddSecurity.CapturedRegistryHighLimb121.actual_complete
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryHighLimb121.full_complete
#print axioms ShielddSecurity.CapturedRegistryHighLimb121.full_complete
