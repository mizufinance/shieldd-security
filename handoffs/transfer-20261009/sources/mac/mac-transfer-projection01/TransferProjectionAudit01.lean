import ShielddSecurity.RuntimeTransferStatement
set_option maxHeartbeats 200000
set_option pp.all true in
#check @ShielddSecurity.TransferStatement.fields_length
#print axioms ShielddSecurity.TransferStatement.fields_length
set_option pp.all true in
#check @ShielddSecurity.TransferStatement.fields_injective
#print axioms ShielddSecurity.TransferStatement.fields_injective
set_option pp.all true in
#check @ShielddSecurity.TransferStatement.equivocation_is_collision
#print axioms ShielddSecurity.TransferStatement.equivocation_is_collision
set_option pp.all true in
#check @ShielddSecurity.RuntimeTransferStatement.projection_exact
#print axioms ShielddSecurity.RuntimeTransferStatement.projection_exact
set_option pp.all true in
#check @ShielddSecurity.RuntimeTransferStatement.projection_injective
#print axioms ShielddSecurity.RuntimeTransferStatement.projection_injective
