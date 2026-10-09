import ShielddSecurity.CompilerColumnRenaming05
namespace ShielddSecurity.CompilerRenamingChecks05
open CompilerColumnRenaming05

def checkRows (rename : Nat → Nat) (actual reference : List Row) : Bool :=
  decide (actual=rows rename reference)
def checkPort (rename : Nat → Nat) (actual reference : Linear) : Bool :=
  decide (actual=linear rename reference)

theorem checked_rows (rename : Nat → Nat) (actual reference : List Row)
    (checked : checkRows rename actual reference=true) : actual=rows rename reference :=
  of_decide_eq_true checked

theorem checked_port (rename : Nat → Nat) (actual reference : Linear)
    (checked : checkPort rename actual reference=true) : actual=linear rename reference :=
  of_decide_eq_true checked

end ShielddSecurity.CompilerRenamingChecks05
set_option pp.all true in
#check @ShielddSecurity.CompilerRenamingChecks05.checked_rows
#print axioms ShielddSecurity.CompilerRenamingChecks05.checked_rows
set_option pp.all true in
#check @ShielddSecurity.CompilerRenamingChecks05.checked_port
#print axioms ShielddSecurity.CompilerRenamingChecks05.checked_port
