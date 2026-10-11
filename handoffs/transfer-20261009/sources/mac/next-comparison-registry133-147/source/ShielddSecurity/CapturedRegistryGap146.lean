import ShielddSecurity.CapturedNextLowShared143
import ShielddSecurity.CapturedRegistryGap145
import ShielddSecurity.LexicographicComparison144
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistryGap146
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F]
abbrev completed := CapturedNextLowShared143.completed (F:=F)
theorem first_high (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) :
    completed base initial next asset value epoch position 981=
      BinaryComparison100.bit (F:=F) (BoundedLimbComparison119.borrow (asset/2^128) (value/2^128)) :=
  (CapturedHighLimbGlobal123.high_frame _ initial next asset value epoch position 981 (by decide) (by decide)).trans
    (CapturedRegistryHighLimb121.borrow_value _ _ _)
theorem first_equal (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) :
    completed base initial next asset value epoch position 1110=
      FieldZeroSeed125.flag (((asset/2^128:Nat):F)-((value/2^128:Nat):F)) :=
  (CapturedHighZeroShared127.zero_frame _ initial next asset value epoch position 1110 (by decide) (by decide)).trans
    (FieldZeroSeed125.flag_value _ _ _)
theorem first_low (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) :
    completed base initial next asset value epoch position 1112=
      BinaryComparison100.bit (F:=F) (BoundedLimbComparison119.borrow (LowBitMeaning128.low asset) (LowBitMeaning128.low value)) :=
  (CapturedLowLimbGlobal131.low_frame _ initial next asset value epoch position 1112 (by decide) (by decide)).trans
    (CapturedRegistryLowLimb130.borrow_value _ _ _)
theorem second_high (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) :
    completed base initial next asset value epoch position 1242=
      BinaryComparison100.bit (F:=F) (BoundedLimbComparison119.borrow (next/2^128) (asset/2^128)) :=
  (CapturedNextHighGlobal135.high_frame _ initial next asset value epoch position 1242 (by decide) (by decide)).trans
    (CapturedNextHighLimb134.borrow_value _ _ _)
theorem second_equal (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) :
    completed base initial next asset value epoch position 1371=
      FieldZeroSeed125.flag (((next/2^128:Nat):F)-((asset/2^128:Nat):F)) :=
  (CapturedNextHighZeroShared139.zero_frame _ initial next asset value epoch position 1371 (by decide) (by decide)).trans
    (FieldZeroSeed125.flag_value _ _ _)
theorem second_low (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) :
    completed base initial next asset value epoch position 1373=
      BinaryComparison100.bit (F:=F) (BoundedLimbComparison119.borrow (LowBitMeaning128.low next) (LowBitMeaning128.low asset)) :=
  (CapturedNextLowGlobal142.low_frame _ initial next asset value epoch position 1373 (by decide) (by decide)).trans
    (CapturedNextLowLimb141.borrow_value _ _ _)
theorem regulated_frame (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) : completed base initial next asset value epoch position 10=base 10 := by
  have early (b : Nat → F) : CapturedNextGlobal118.completed b initial next asset value epoch position 10=b 10 :=
    (CapturedRegulatedAsset96.outside_early _ initial epoch position 10 (by decide) (by decide) (by decide)).trans
      ((CapturedRegistryValueRange97.completed_outside _ value 10 (Or.inl (by decide))).trans
        ((CapturedRegistryAssetRange109.completed_outside _ asset 10 (Or.inl (by decide))).trans
          (CapturedRegistryNextRange114.completed_outside b next 10 (Or.inl (by decide)))))
  exact (early _).trans
    ((CapturedRegistryHighLimb121.outside _ _ _ 10 (Or.inl (by decide))).trans
      ((FieldZeroSeed125.outside _ 1110 _ 10 (Or.inl (by decide))).trans
        ((CapturedRegistryLowLimb130.outside _ _ _ 10 (Or.inl (by decide))).trans
          ((CapturedNextHighLimb134.outside _ _ _ 10 (Or.inl (by decide))).trans
            ((FieldZeroSeed125.outside _ 1371 _ 10 (Or.inl (by decide))).trans
              (CapturedNextLowLimb141.outside base _ _ 10 (Or.inl (by decide))))))))
variable [CharP F p]
theorem gap_zero (c : TransferSem.Crypto) (w : TransferSem.Witness) (legal : TransferSem.RegistrySem c w)
    (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (regulated : base 10=(if w.regulated then 1 else 0)) (zero : base 0=1) :
    completed base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position 33788=0 := by
  have aBound : w.asset<2^255 := Nat.lt_trans legal.2.2.2.2.2.2.2.1 (show p<2^255 by decide)
  have vBound : w.registry.value<2^255 := Nat.lt_trans legal.2.2.2.2.2.2.1 (show p<2^255 by decide)
  have nBound : w.registry.nextValue<2^255 := Nat.lt_trans legal.2.2.2.2.2.2.2.2.1 (show p<2^255 by decide)
  have h:=CapturedRegistryGap145.gap_polynomial
    (completed base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position)
    (CapturedNextLowGlobal142.arithmetic _ _ _ _ _ _ _)
    (CapturedNextLowGlobal142.zero _ _ _ _ _ _ _ zero)
    (CapturedGlobalRegistered74.completed_copy _ _)
  rw [first_high,first_equal,first_low,second_high,second_equal,second_low,regulated_frame,regulated,
    LexicographicComparison144.lex_field w.asset w.registry.value aBound vBound,
    LexicographicComparison144.lex_field w.registry.nextValue w.asset nBound aBound] at h
  cases flag : w.regulated
  · have branch:=legal.2.2.2.2.2.2.2.2.2.2
    simp only [flag,Bool.false_eq_true,if_false] at branch
    have noFirst : ¬w.asset≤w.registry.value := by omega
    have noSecond : ¬w.registry.nextValue≤w.asset := by omega
    simpa only [flag,Bool.false_eq_true,if_false,if_neg noFirst,if_neg noSecond,sub_zero,mul_one,sub_self,mul_zero] using h
  · simpa only [flag,if_true,sub_self,zero_mul] using h
noncomputable def actualRows : List Row := [⟨[(33788,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩]
def normalizedRows : List Row := [⟨[(33788,-1)],[]⟩]
noncomputable def positionCheck : Bool := decide (CapturedAssertions50B0005.block.actual 187=actualRows[0]?)
theorem position_checked : positionCheck=true := by decide +kernel
theorem actual_position (index : Nat) (bound : index<1) :
    CapturedFullRelation58.rowAt (179421+index)=actualRows[index]? := by
  have eq : index=0 := by omega
  subst index
  have leaf := of_decide_eq_true position_checked
  have root : CapturedFullRelation58.rowAt 179421=CapturedAssertions50B0005.block.actual 187 := rfl
  exact root.trans leaf
noncomputable def reverseCheck : Bool := CompilerIndexed01.checkOriginalCoverage p 0
  actualRows.toArray normalizedRows.toArray (List.range actualRows.length).toArray
theorem reverse_checked : reverseCheck=true := by decide +kernel
theorem complete (c : TransferSem.Crypto) (w : TransferSem.Witness) (legal : TransferSem.RegistrySem c w)
    (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (regulated : base 10=(if w.regulated then 1 else 0)) (zero : base 0=1) :
    SatisfiesAt (completed base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (179421+index)) 1 := by
  let rho:=completed base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position
  have value : rho 33788=0 := gap_zero c w legal base initial regulated zero
  have normal : Satisfies rho normalizedRows := by
    intro row member
    have same : row=⟨[(33788,-1)],[]⟩ := by simpa only [normalizedRows,List.mem_singleton] using member
    subst row
    change Square (eval rho [(33788,-1)]) (eval rho [])
    simp only [eval,value,Int.cast_neg,Int.cast_one,mul_zero,add_zero,Square]
  have actual:=transfer rho actualRows normalizedRows reverse_checked normal
  intro index bound row found
  exact actual row (List.mem_iff_getElem?.mpr ⟨index,(actual_position index bound).symm.trans found⟩)
end ShielddSecurity.CapturedRegistryGap146

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap146.completed
#print axioms ShielddSecurity.CapturedRegistryGap146.completed
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap146.first_high
#print axioms ShielddSecurity.CapturedRegistryGap146.first_high
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap146.first_equal
#print axioms ShielddSecurity.CapturedRegistryGap146.first_equal
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap146.first_low
#print axioms ShielddSecurity.CapturedRegistryGap146.first_low
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap146.second_high
#print axioms ShielddSecurity.CapturedRegistryGap146.second_high
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap146.second_equal
#print axioms ShielddSecurity.CapturedRegistryGap146.second_equal
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap146.second_low
#print axioms ShielddSecurity.CapturedRegistryGap146.second_low
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap146.regulated_frame
#print axioms ShielddSecurity.CapturedRegistryGap146.regulated_frame
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap146.gap_zero
#print axioms ShielddSecurity.CapturedRegistryGap146.gap_zero
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap146.actualRows
#print axioms ShielddSecurity.CapturedRegistryGap146.actualRows
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap146.normalizedRows
#print axioms ShielddSecurity.CapturedRegistryGap146.normalizedRows
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap146.positionCheck
#print axioms ShielddSecurity.CapturedRegistryGap146.positionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap146.position_checked
#print axioms ShielddSecurity.CapturedRegistryGap146.position_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap146.actual_position
#print axioms ShielddSecurity.CapturedRegistryGap146.actual_position
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap146.reverseCheck
#print axioms ShielddSecurity.CapturedRegistryGap146.reverseCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap146.reverse_checked
#print axioms ShielddSecurity.CapturedRegistryGap146.reverse_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap146.complete
#print axioms ShielddSecurity.CapturedRegistryGap146.complete
