import ShielddSecurity.TransferPoseidonUpstream11ProbeData01
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.TransferPoseidonUpstream11B1R0Probe01
open Compiler Poseidon PoseidonIndexedFolded02 TransferPoseidonCall04Shared01 TransferPoseidonUpstream11ProbeData01
theorem column0_checked : checkColumn p copy B1R0Rows parameters 0 B1R0before B1R0after_ark B1R0after_sbox B1R0Hints 0=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R0Probe01.column0_checked
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R0Probe01.column0_checked

theorem column1_checked : checkColumn p copy B1R0Rows parameters 0 B1R0before B1R0after_ark B1R0after_sbox B1R0Hints 1=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R0Probe01.column1_checked
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R0Probe01.column1_checked

theorem column2_checked : checkColumn p copy B1R0Rows parameters 0 B1R0before B1R0after_ark B1R0after_sbox B1R0Hints 2=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R0Probe01.column2_checked
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R0Probe01.column2_checked

theorem column3_checked : checkColumn p copy B1R0Rows parameters 0 B1R0before B1R0after_ark B1R0after_sbox B1R0Hints 3=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R0Probe01.column3_checked
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R0Probe01.column3_checked

theorem column4_checked : checkColumn p copy B1R0Rows parameters 0 B1R0before B1R0after_ark B1R0after_sbox B1R0Hints 4=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R0Probe01.column4_checked
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R0Probe01.column4_checked

theorem column5_checked : checkColumn p copy B1R0Rows parameters 0 B1R0before B1R0after_ark B1R0after_sbox B1R0Hints 5=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R0Probe01.column5_checked
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R0Probe01.column5_checked

theorem mix0_checked : canonical p (B1R0after 0)=canonical p (mixLinear parameters.mds B1R0after_sbox 0) := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R0Probe01.mix0_checked
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R0Probe01.mix0_checked

theorem mix1_checked : canonical p (B1R0after 1)=canonical p (mixLinear parameters.mds B1R0after_sbox 1) := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R0Probe01.mix1_checked
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R0Probe01.mix1_checked

theorem mix2_checked : canonical p (B1R0after 2)=canonical p (mixLinear parameters.mds B1R0after_sbox 2) := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R0Probe01.mix2_checked
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R0Probe01.mix2_checked

theorem mix3_checked : canonical p (B1R0after 3)=canonical p (mixLinear parameters.mds B1R0after_sbox 3) := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R0Probe01.mix3_checked
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R0Probe01.mix3_checked

theorem mix4_checked : canonical p (B1R0after 4)=canonical p (mixLinear parameters.mds B1R0after_sbox 4) := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R0Probe01.mix4_checked
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R0Probe01.mix4_checked

theorem mix5_checked : canonical p (B1R0after 5)=canonical p (mixLinear parameters.mds B1R0after_sbox 5) := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R0Probe01.mix5_checked
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R0Probe01.mix5_checked

theorem absorption_checked : Poseidon.checkAbsorb p B1before_absorption B1Chunk B1absorbed=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R0Probe01.absorption_checked
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R0Probe01.absorption_checked

end ShielddSecurity.TransferPoseidonUpstream11B1R0Probe01
