import ShielddSecurity.AuthorizationCompleteWindows456
import ShielddSecurity.AuthorizationWindows459
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationWindowSchedule460
open VariableWindowLayout447 AuthorizationWindowRows455
open AuthorizationCompleteWindows456 (entries)
def key (b : BoundEntry) : Nat × Nat × Nat × Nat :=
  (b.family.baseX,b.family.precomputeX,b.family.assertionStart,b.window)
def expected (j : Nat) : Nat × Nat × Nat × Nat :=
  (1504+16*(j/125),2253+756*(j/125),2257+758*(j/125),j%125+1)
theorem schedule : entries.map key=(List.range 250).map expected := by
  rw [show entries.map key=entries.map
    (fun b => (b.family.baseX,b.family.precomputeX,b.family.assertionStart,b.window)) from rfl,
    AuthorizationCompleteWindows456.schedule]
  decide +kernel

theorem entry (j : Nat) (bound : j<250) :
    ∃ e, (⟨family (j/125),j%125+1,e⟩ : BoundEntry)∈entries := by
  have member : expected j∈entries.map key := by
    rw [schedule]
    exact List.mem_map.mpr ⟨j,List.mem_range.mpr bound,rfl⟩
  obtain ⟨⟨⟨baseX,precomputeX,assertionStart⟩,window,e⟩,inside,equal⟩ := List.mem_map.mp member
  change (baseX,precomputeX,assertionStart,window)=expected j at equal
  simp only [expected,Prod.mk.injEq] at equal
  rcases equal with ⟨rfl,rfl,rfl,rfl⟩
  exact ⟨e,inside⟩

theorem window_entry (index window : Nat) (bound : index<2) (lower : 1≤window) (upper : window<126) :
    ∃ e, check ⟨family index,window,e⟩=true := by
  have jBound : index*125+(window-1)<250 := by omega
  obtain ⟨e,member⟩ := entry (index*125+(window-1)) jBound
  have quotient : (index*125+(window-1))/125=index := by omega
  have remainder : (index*125+(window-1))%125+1=window := by omega
  rw [quotient,remainder] at member
  exact ⟨e,List.all_eq_true.mp AuthorizationCompleteWindows456.checked _ member⟩
end ShielddSecurity.AuthorizationWindowSchedule460

set_option pp.all true in
#check @ShielddSecurity.AuthorizationWindowSchedule460.key
#print axioms ShielddSecurity.AuthorizationWindowSchedule460.key

set_option pp.all true in
#check @ShielddSecurity.AuthorizationWindowSchedule460.expected
#print axioms ShielddSecurity.AuthorizationWindowSchedule460.expected

set_option pp.all true in
#check @ShielddSecurity.AuthorizationWindowSchedule460.schedule
#print axioms ShielddSecurity.AuthorizationWindowSchedule460.schedule

set_option pp.all true in
#check @ShielddSecurity.AuthorizationWindowSchedule460.entry
#print axioms ShielddSecurity.AuthorizationWindowSchedule460.entry

set_option pp.all true in
#check @ShielddSecurity.AuthorizationWindowSchedule460.window_entry
#print axioms ShielddSecurity.AuthorizationWindowSchedule460.window_entry
