import ShielddSecurity.Compiler
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedInitial73419Collected01
open Compiler
def collected (rows : List Row) : List Row := rows.map (fun row => ⟨collect row.a, collect row.b⟩)
theorem transfer {F : Type} [Field F] (target source : List Row)
    (equal : target = collected source) (rho : Nat → F) (satisfied : Satisfies rho source) :
    Satisfies rho target := by
  rw [equal]
  intro value member
  obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
  simpa only [eval_collect] using satisfied original present
end ShielddSecurity.CapturedInitial73419Collected01
set_option pp.all true in
#check @ShielddSecurity.CapturedInitial73419Collected01.collected
#print axioms ShielddSecurity.CapturedInitial73419Collected01.collected
set_option pp.all true in
#check @ShielddSecurity.CapturedInitial73419Collected01.transfer
#print axioms ShielddSecurity.CapturedInitial73419Collected01.transfer
