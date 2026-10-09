import ShielddSecurity.CompilerColumnRenaming05
namespace ShielddSecurity.CompilerWindowRenaming05

-- Swap two disjoint finite windows, so translation on the source window is globally injective.
def swap (start width offset column : Nat) : Nat :=
  if start≤column ∧ column<start+width then column+offset
  else if start+offset≤column ∧ column<start+offset+width then column-offset
  else column

theorem involutive (start width offset : Nat) (separate : width≤offset) (column : Nat) :
    swap start width offset (swap start width offset column)=column := by
  unfold swap
  split_ifs <;> omega

theorem injective (start width offset : Nat) (separate : width≤offset) :
    Function.Injective (swap start width offset) := by
  intro left right equality
  have result := congrArg (swap start width offset) equality
  simpa only [involutive start width offset separate] using result

theorem translated (start width offset column : Nat)
    (lower : start≤column) (upper : column<start+width) : swap start width offset column=column+offset := by
  simp [swap,lower,upper]

theorem below_fixed (start width offset column : Nat) (below : column<start) :
    swap start width offset column=column := by
  unfold swap
  split_ifs <;> omega

theorem above_fixed (start width offset column : Nat) (separate : width≤offset)
    (above : start+offset+width≤column) : swap start width offset column=column := by
  unfold swap
  split_ifs <;> omega

end ShielddSecurity.CompilerWindowRenaming05
set_option pp.all true in
#check @ShielddSecurity.CompilerWindowRenaming05.involutive
#print axioms ShielddSecurity.CompilerWindowRenaming05.involutive
set_option pp.all true in
#check @ShielddSecurity.CompilerWindowRenaming05.injective
#print axioms ShielddSecurity.CompilerWindowRenaming05.injective
set_option pp.all true in
#check @ShielddSecurity.CompilerWindowRenaming05.translated
#print axioms ShielddSecurity.CompilerWindowRenaming05.translated
set_option pp.all true in
#check @ShielddSecurity.CompilerWindowRenaming05.below_fixed
#print axioms ShielddSecurity.CompilerWindowRenaming05.below_fixed
set_option pp.all true in
#check @ShielddSecurity.CompilerWindowRenaming05.above_fixed
#print axioms ShielddSecurity.CompilerWindowRenaming05.above_fixed
