import ShielddSecurity.TransferPoseidonUpstream11ProbeData01
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.TransferPoseidonUpstream11TailLeafProbe01
open Compiler CompilerRenamingChecks05 TransferPoseidonUpstream11ProbeData01
theorem B0_checked : checkRows B0Rename B0R2Rows TransferPoseidonCall04R02.arithmeticRows.toList=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11TailLeafProbe01.B0_checked
#print axioms ShielddSecurity.TransferPoseidonUpstream11TailLeafProbe01.B0_checked

theorem B0_exact : B0R2Rows=CompilerColumnRenaming05.rows B0Rename TransferPoseidonCall04R02.arithmeticRows.toList := checked_rows _ _ _ B0_checked
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11TailLeafProbe01.B0_exact
#print axioms ShielddSecurity.TransferPoseidonUpstream11TailLeafProbe01.B0_exact

theorem B1_checked : checkRows B1Rename B1R2Rows TransferPoseidonCall04R02.arithmeticRows.toList=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11TailLeafProbe01.B1_checked
#print axioms ShielddSecurity.TransferPoseidonUpstream11TailLeafProbe01.B1_checked

theorem B1_exact : B1R2Rows=CompilerColumnRenaming05.rows B1Rename TransferPoseidonCall04R02.arithmeticRows.toList := checked_rows _ _ _ B1_checked
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11TailLeafProbe01.B1_exact
#print axioms ShielddSecurity.TransferPoseidonUpstream11TailLeafProbe01.B1_exact

end ShielddSecurity.TransferPoseidonUpstream11TailLeafProbe01
