import ShielddSecurity.WordHints210
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedWordFlags220
open WordHints210 CompilerAssertionBlock51
def Coherent (entries : List (Nat × Bool)) : Prop :=
 ∀ pair∈entries,∀ other∈entries,pair.1=other.1 → pair.2=other.2
def chosen (entries : List (Nat × Bool)) (fallback : Nat → Bool) (column : Nat) : Bool :=
 match entries with
 | [] => fallback column
 | pair::rest => if column=pair.1 then pair.2 else chosen rest fallback column
theorem chosen_eq (entries : List (Nat × Bool)) (fallback : Nat → Bool)
 (coherent : Coherent entries) (pair : Nat × Bool) (member : pair∈entries) :
 chosen entries fallback pair.1=pair.2 := by
 revert coherent member
 induction entries with
 | nil =>
   intro coherent member
   simp only [List.not_mem_nil] at member
 | cons head rest ih =>
   intro coherent member
   rcases List.mem_cons.mp member with samePair|tail
   · subst pair
     change (if head.1=head.1 then head.2 else chosen rest fallback head.1)=head.2
     exact if_pos rfl
   · by_cases same : pair.1=head.1
     · exact (if_pos same).trans (coherent pair member head (List.mem_cons_self ..) same).symm
     · change (if pair.1=head.1 then head.2 else chosen rest fallback pair.1)=pair.2
       rw [if_neg same]
       apply ih ?_ tail
       intro left leftMember right rightMember equal
       exact coherent left (List.mem_cons_of_mem head leftMember)
         right (List.mem_cons_of_mem head rightMember) equal
theorem chosen_outside (entries : List (Nat × Bool)) (fallback : Nat → Bool) (column : Nat)
 (outside : column∉entries.map Prod.fst) : chosen entries fallback column=fallback column := by
 revert outside
 induction entries with
 | nil => intro outside;rfl
 | cons head rest ih =>
   intro outside
   have different : column≠head.1 := by
     intro same
     apply outside
     exact List.mem_map.mpr ⟨head,List.mem_cons_self ..,same.symm⟩
   change (if column=head.1 then head.2 else chosen rest fallback column)=fallback column
   rw [if_neg different]
   apply ih
   intro member
   exact outside (List.mem_cons_of_mem head.1 member)
theorem map_eq_of_pairs (fields : List Nat) (values : List Bool) (flags : Nat → Bool)
 (sameLength : fields.length=values.length)
 (matching : ∀ pair∈fields.zip values,flags pair.1=pair.2) : fields.map flags=values := by
 revert sameLength matching
 induction fields generalizing values with
 | nil =>
   intro sameLength matching
   have empty : values=[] := List.length_eq_zero_iff.mp sameLength.symm
   subst values
   rfl
 | cons field rest ih =>
   intro sameLength matching
   cases values with
   | nil => simp only [List.length_cons,List.length_nil] at sameLength;omega
   | cons value values =>
     have first := matching (field,value) (List.mem_cons_self ..)
     change flags field :: rest.map flags=value::values
     rw [first]
     congr 1
     apply ih values (by simpa only [List.length_cons,Nat.add_right_cancel_iff] using sameLength)
     intro pair member
     exact matching pair (List.mem_cons_of_mem (field,value) member)
def assignments (slots : List Slot) (numbers : Nat → Nat) : List (Nat × Bool) :=
 slots.flatMap fun slot => (columns slot).zip (encodeBits slot.width (numbers slot.value))
def flags (slots : List Slot) (numbers : Nat → Nat) (fallback : Nat → Bool) : Nat → Bool :=
 chosen (assignments slots numbers) fallback
theorem encoded (slots : List Slot) (numbers : Nat → Nat) (fallback : Nat → Bool)
 (coherent : Coherent (assignments slots numbers)) (slot : Slot) (member : slot∈slots) :
 (columns slot).map (flags slots numbers fallback)=encodeBits slot.width (numbers slot.value) := by
 apply map_eq_of_pairs
 · simp only [columns,List.length_range',encodeBits_length]
 · intro pair present
   exact chosen_eq (assignments slots numbers) fallback coherent pair
     (List.mem_flatMap.mpr ⟨slot,member,present⟩)
end ShielddSecurity.SharedWordFlags220

set_option pp.all true in
#check @ShielddSecurity.SharedWordFlags220.Coherent
#print axioms ShielddSecurity.SharedWordFlags220.Coherent
set_option pp.all true in
#check @ShielddSecurity.SharedWordFlags220.chosen
#print axioms ShielddSecurity.SharedWordFlags220.chosen
set_option pp.all true in
#check @ShielddSecurity.SharedWordFlags220.chosen_eq
#print axioms ShielddSecurity.SharedWordFlags220.chosen_eq
set_option pp.all true in
#check @ShielddSecurity.SharedWordFlags220.chosen_outside
#print axioms ShielddSecurity.SharedWordFlags220.chosen_outside
set_option pp.all true in
#check @ShielddSecurity.SharedWordFlags220.map_eq_of_pairs
#print axioms ShielddSecurity.SharedWordFlags220.map_eq_of_pairs
set_option pp.all true in
#check @ShielddSecurity.SharedWordFlags220.assignments
#print axioms ShielddSecurity.SharedWordFlags220.assignments
set_option pp.all true in
#check @ShielddSecurity.SharedWordFlags220.flags
#print axioms ShielddSecurity.SharedWordFlags220.flags
set_option pp.all true in
#check @ShielddSecurity.SharedWordFlags220.encoded
#print axioms ShielddSecurity.SharedWordFlags220.encoded
