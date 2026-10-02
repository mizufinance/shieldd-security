import ShielddSecurity.PermanentSpend
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
set_option pp.all true
#check ShielddSecurity.PermanentSpend.branch_sound
#print ShielddSecurity.PermanentSpend.branch_sound
#print axioms ShielddSecurity.PermanentSpend.branch_sound
#check ShielddSecurity.PermanentSpend.branch_gates_complete
#print ShielddSecurity.PermanentSpend.branch_gates_complete
#print axioms ShielddSecurity.PermanentSpend.branch_gates_complete
#check ShielddSecurity.PermanentSpend.assignment_branch_sound
#print ShielddSecurity.PermanentSpend.assignment_branch_sound
#print axioms ShielddSecurity.PermanentSpend.assignment_branch_sound
#check ShielddSecurity.PermanentSpend.required_input_real
#print ShielddSecurity.PermanentSpend.required_input_real
#print axioms ShielddSecurity.PermanentSpend.required_input_real
#check ShielddSecurity.PermanentSpend.required_assignment_real
#print ShielddSecurity.PermanentSpend.required_assignment_real
#print axioms ShielddSecurity.PermanentSpend.required_assignment_real
-- Helper inspection is separate from the five canonical theorem audits.
#check ShielddSecurity.boolean_sound
#print ShielddSecurity.boolean_sound
#print axioms ShielddSecurity.boolean_sound
#print ShielddSecurity.Square
#print ShielddSecurity.Linear
#print ShielddSecurity.eval
#print ShielddSecurity.PermanentSpend.BranchSpec

-- Additional Defs-only helpers; canonical five remain unchanged above.
#check ShielddSecurity.PermanentSpend.sub_zero_field
#print ShielddSecurity.PermanentSpend.sub_zero_field
#print axioms ShielddSecurity.PermanentSpend.sub_zero_field
#check ShielddSecurity.PermanentSpend.eq_of_sub_zero_field
#print ShielddSecurity.PermanentSpend.eq_of_sub_zero_field
#print axioms ShielddSecurity.PermanentSpend.eq_of_sub_zero_field
