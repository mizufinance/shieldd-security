import ShielddSecurity.CapturedArithmetic45B0000
import ShielddSecurity.CapturedArithmetic45B0001
import ShielddSecurity.CapturedArithmetic45B0002
import ShielddSecurity.CapturedArithmetic45B0003
import ShielddSecurity.CapturedArithmetic45B0004
import ShielddSecurity.CapturedArithmetic45B0005
import ShielddSecurity.CapturedArithmetic45B0006
import ShielddSecurity.CapturedArithmetic45B0007
import ShielddSecurity.CompilerArithmeticBlock44
import ShielddSecurity.CompilerArithmeticTransport41
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedArithmeticGroup46
open CompilerArithmeticBlock44 CompilerArithmeticTransport41
noncomputable def block : Block ArithmeticCoefficients39.value copy 22738 1852 := (append ArithmeticCoefficients39.value copy 22738 1034 818 (append ArithmeticCoefficients39.value copy 22738 624 410 (append ArithmeticCoefficients39.value copy 22738 512 112 CapturedArithmetic45B0000.block CapturedArithmetic45B0001.block) (append ArithmeticCoefficients39.value copy 23362 291 119 CapturedArithmetic45B0002.block CapturedArithmetic45B0003.block)) (append ArithmeticCoefficients39.value copy 23772 410 408 (append ArithmeticCoefficients39.value copy 23772 282 128 CapturedArithmetic45B0004.block CapturedArithmetic45B0005.block) (append ArithmeticCoefficients39.value copy 24182 268 140 CapturedArithmetic45B0006.block CapturedArithmetic45B0007.block)))
noncomputable def rowAt := block.actual
theorem every_position (index : Nat) (bound : index<1852) : ∃ row : Row,rowAt index=some row :=
  CompilerArithmeticBlock44.every_position ArithmeticCoefficients39.value copy 22738 1852 block index bound
theorem exact_reverse (index : Nat) (row : Row) : rowAt index=some row ↔
    CompilerCachedArithmetic42.rowAt ArithmeticCoefficients39.value 22738 block.tree index=some row :=
  CompilerArithmeticBlock44.exact_reverse ArithmeticCoefficients39.value copy 22738 1852 block index row
variable {F : Type} [Field F] [CharP F p]
noncomputable def completed (base : Nat → F) := CompilerArithmeticBlock44.completed ArithmeticCoefficients39.value copy 22738 1852 block base
omit [CharP F p] in
theorem outside (base : Nat → F) (column : Nat) (bound : column<22738 ∨ 24590≤column) : completed base column=base column :=
  CompilerArithmeticBlock44.outside ArithmeticCoefficients39.value copy 22738 1852 block base column bound
theorem complete (base : Nat → F) : CompilerArithmeticBlock44.SatisfiesAt (completed base) rowAt 1852 :=
  CompilerArithmeticBlock44.complete ArithmeticCoefficients39.value copy 22738 1852 block base (by decide) (four_ne_zero (F:=F))
omit [CharP F p] in
theorem original_inputs (base : Nat → F) (input : Nat) (bound : input<22735) : completed base (3+input)=base (3+input) :=
  CompilerArithmeticBlock44.inputs ArithmeticCoefficients39.value copy 1852 block base input bound
omit [CharP F p] in
theorem fixed (base : Nat → F) : completed base 0=base 0 ∧ completed base 1=base 1 ∧ completed base 2=base 2 ∧ completed base copy=base copy :=
  CompilerArithmeticBlock44.fixed ArithmeticCoefficients39.value copy 22738 1852 block base (by decide) (by decide)
theorem shared_copy (base : Nat → F) (linked : base copy=base 0) :
    Square (eval (completed base) [(0,1),(copy,-1)]) (eval (completed base) []) := by
  simp only [eval,Int.cast_one,Int.cast_neg,one_mul,neg_one_mul,add_zero,
    outside base 0 (Or.inl (by decide)),outside base copy (Or.inr (by decide)),linked,add_neg_cancel]
  simp [Square]
end ShielddSecurity.CapturedArithmeticGroup46

set_option pp.all true in
#check @ShielddSecurity.CapturedArithmeticGroup46.block
#print axioms ShielddSecurity.CapturedArithmeticGroup46.block
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmeticGroup46.rowAt
#print axioms ShielddSecurity.CapturedArithmeticGroup46.rowAt
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmeticGroup46.every_position
#print axioms ShielddSecurity.CapturedArithmeticGroup46.every_position
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmeticGroup46.exact_reverse
#print axioms ShielddSecurity.CapturedArithmeticGroup46.exact_reverse
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmeticGroup46.completed
#print axioms ShielddSecurity.CapturedArithmeticGroup46.completed
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmeticGroup46.outside
#print axioms ShielddSecurity.CapturedArithmeticGroup46.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmeticGroup46.complete
#print axioms ShielddSecurity.CapturedArithmeticGroup46.complete
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmeticGroup46.original_inputs
#print axioms ShielddSecurity.CapturedArithmeticGroup46.original_inputs
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmeticGroup46.fixed
#print axioms ShielddSecurity.CapturedArithmeticGroup46.fixed
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmeticGroup46.shared_copy
#print axioms ShielddSecurity.CapturedArithmeticGroup46.shared_copy
