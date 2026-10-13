import ShielddSecurity.CapturedFourSubgroupConstructor88
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationRkCapture506B05
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
def rename (column : Nat) : Nat :=
  if 14≤column ∧ column<21 then 4272+(column-14)
  else if 22738≤column ∧ column<22802 then 64462+(column-22738)
  else column

def arithmeticRows : List Row :=
  CompilerColumnRenaming05.rows rename TransferFirstSubgroupData01.arithmeticRows.toList

def originalRows : List Row :=
  CompilerColumnRenaming05.rows rename TransferFirstSubgroupData01.originalRows.toList

end ShielddSecurity.AuthorizationRkCapture506B05
set_option pp.all true in
#check @ShielddSecurity.AuthorizationRkCapture506B05.rename
#print axioms ShielddSecurity.AuthorizationRkCapture506B05.rename

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRkCapture506B05.arithmeticRows
#print axioms ShielddSecurity.AuthorizationRkCapture506B05.arithmeticRows

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRkCapture506B05.originalRows
#print axioms ShielddSecurity.AuthorizationRkCapture506B05.originalRows
