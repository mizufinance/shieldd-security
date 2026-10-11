import ShielddSecurity.CapturedArithmetic52G00
import ShielddSecurity.CapturedArithmetic52G01
import ShielddSecurity.CapturedArithmetic52G02
import ShielddSecurity.CapturedArithmetic52G03
import ShielddSecurity.CapturedArithmetic52G04
import ShielddSecurity.CapturedArithmetic52G05
import ShielddSecurity.CapturedArithmetic52G06
import ShielddSecurity.CapturedArithmetic52G07
import ShielddSecurity.CapturedArithmetic52G08
import ShielddSecurity.CapturedArithmetic52G09
import ShielddSecurity.CompilerArithmeticFixed48
import ShielddSecurity.CompilerArithmeticUniqueness49
import ShielddSecurity.CompilerArithmeticTransport41
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedFullArithmetic52
open CompilerArithmeticTransport41
noncomputable def block : CompilerArithmeticBlock44.Block ArithmeticCoefficients39.value copy 22738 177954 := (CompilerArithmeticBlock44.append ArithmeticCoefficients39.value copy 22738 83708 94246 (CompilerArithmeticBlock44.append ArithmeticCoefficients39.value copy 22738 28302 55406 (CompilerArithmeticBlock44.append ArithmeticCoefficients39.value copy 22738 14381 13921 CapturedArithmetic52G00.block CapturedArithmetic52G01.block) (CompilerArithmeticBlock44.append ArithmeticCoefficients39.value copy 51040 20522 34884 CapturedArithmetic52G02.block (CompilerArithmeticBlock44.append ArithmeticCoefficients39.value copy 71562 13004 21880 CapturedArithmetic52G03.block CapturedArithmetic52G04.block))) (CompilerArithmeticBlock44.append ArithmeticCoefficients39.value copy 106446 38761 55485 (CompilerArithmeticBlock44.append ArithmeticCoefficients39.value copy 106446 12938 25823 CapturedArithmetic52G05.block CapturedArithmetic52G06.block) (CompilerArithmeticBlock44.append ArithmeticCoefficients39.value copy 145207 30154 25331 CapturedArithmetic52G07.block (CompilerArithmeticBlock44.append ArithmeticCoefficients39.value copy 175361 20947 4384 CapturedArithmetic52G08.block CapturedArithmetic52G09.block))))
noncomputable def rowAt := block.actual
theorem every_position (index : Nat) (bound : index<177954) : ∃ row, rowAt index=some row :=
  CompilerArithmeticBlock44.every_position ArithmeticCoefficients39.value copy 22738 177954 block index bound
theorem exact_reverse (index : Nat) (row : Row) : rowAt index=some row ↔
    CompilerCachedArithmetic42.rowAt ArithmeticCoefficients39.value 22738 block.tree index=some row :=
  CompilerArithmeticBlock44.exact_reverse ArithmeticCoefficients39.value copy 22738 177954 block index row
variable {F : Type} [Field F] [CharP F p]
noncomputable def completed (base : Nat → F) :=
  CompilerArithmeticBlock44.completed ArithmeticCoefficients39.value copy 22738 177954 block base
theorem complete (base : Nat → F) : CompilerArithmeticBlock44.SatisfiesAt (completed base) rowAt 177954 :=
  CompilerArithmeticBlock44.complete ArithmeticCoefficients39.value copy 22738 177954 block base (by decide) (CompilerArithmeticTransport41.four_ne_zero (F:=F))
omit [CharP F p] in
theorem outside (base : Nat → F) (column : Nat) (bound : column<22738 ∨ 200692≤column) : completed base column=base column :=
  CompilerArithmeticBlock44.outside ArithmeticCoefficients39.value copy 22738 177954 block base column bound
omit [CharP F p] in
theorem original_inputs (base : Nat → F) (input : Nat) (bound : input<22735) : completed base (3+input)=base (3+input) :=
  CompilerArithmeticBlock44.inputs ArithmeticCoefficients39.value copy 177954 block base input bound
omit [CharP F p] in
theorem fixed (base : Nat → F) : completed base 0=base 0 ∧ completed base 1=base 1 ∧ completed base 2=base 2 ∧ completed base copy=base copy :=
  CompilerArithmeticBlock44.fixed ArithmeticCoefficients39.value copy 22738 177954 block base (by decide) (by decide)
theorem fixed_point (rho : Nat → F) (sat : CompilerArithmeticBlock44.SatisfiesAt rho rowAt 177954) : completed rho=rho :=
  CompilerArithmeticFixed48.block_fixed ArithmeticCoefficients39.value copy 22738 177954 block rho sat (CompilerArithmeticTransport41.four_ne_zero (F:=F))
theorem unique_completed (base rho : Nat → F)
    (agree : CompilerArithmeticUniqueness49.PrefixAgreement copy 22738 base rho)
    (sat : CompilerArithmeticBlock44.SatisfiesAt rho rowAt 177954) :
    CompilerArithmeticUniqueness49.PrefixAgreement copy 200692 (completed base) rho :=
  CompilerArithmeticUniqueness49.unique_completed ArithmeticCoefficients39.value copy 22738 177954 block base rho sat agree (CompilerArithmeticTransport41.four_ne_zero (F:=F))
theorem satisfying_unique (rho sigma : Nat → F)
    (agree : CompilerArithmeticUniqueness49.PrefixAgreement copy 22738 rho sigma)
    (left : CompilerArithmeticBlock44.SatisfiesAt rho rowAt 177954)
    (right : CompilerArithmeticBlock44.SatisfiesAt sigma rowAt 177954) :
    CompilerArithmeticUniqueness49.PrefixAgreement copy 200692 rho sigma := by
  have determined:=unique_completed rho sigma agree right
  rw [fixed_point rho left] at determined
  exact determined
end ShielddSecurity.CapturedFullArithmetic52

set_option pp.all true in
#check @ShielddSecurity.CapturedFullArithmetic52.block
#print axioms ShielddSecurity.CapturedFullArithmetic52.block
set_option pp.all true in
#check @ShielddSecurity.CapturedFullArithmetic52.rowAt
#print axioms ShielddSecurity.CapturedFullArithmetic52.rowAt
set_option pp.all true in
#check @ShielddSecurity.CapturedFullArithmetic52.every_position
#print axioms ShielddSecurity.CapturedFullArithmetic52.every_position
set_option pp.all true in
#check @ShielddSecurity.CapturedFullArithmetic52.exact_reverse
#print axioms ShielddSecurity.CapturedFullArithmetic52.exact_reverse
set_option pp.all true in
#check @ShielddSecurity.CapturedFullArithmetic52.completed
#print axioms ShielddSecurity.CapturedFullArithmetic52.completed
set_option pp.all true in
#check @ShielddSecurity.CapturedFullArithmetic52.complete
#print axioms ShielddSecurity.CapturedFullArithmetic52.complete
set_option pp.all true in
#check @ShielddSecurity.CapturedFullArithmetic52.outside
#print axioms ShielddSecurity.CapturedFullArithmetic52.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedFullArithmetic52.original_inputs
#print axioms ShielddSecurity.CapturedFullArithmetic52.original_inputs
set_option pp.all true in
#check @ShielddSecurity.CapturedFullArithmetic52.fixed
#print axioms ShielddSecurity.CapturedFullArithmetic52.fixed
set_option pp.all true in
#check @ShielddSecurity.CapturedFullArithmetic52.fixed_point
#print axioms ShielddSecurity.CapturedFullArithmetic52.fixed_point
set_option pp.all true in
#check @ShielddSecurity.CapturedFullArithmetic52.unique_completed
#print axioms ShielddSecurity.CapturedFullArithmetic52.unique_completed
set_option pp.all true in
#check @ShielddSecurity.CapturedFullArithmetic52.satisfying_unique
#print axioms ShielddSecurity.CapturedFullArithmetic52.satisfying_unique
