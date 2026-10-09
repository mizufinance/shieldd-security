import ShielddSecurity.TransferPoseidonRound04SemanticData01
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.TransferPoseidonRound04SemanticChecks01
open Compiler CompilerIndexed01 Poseidon PoseidonIndexedRound01 TransferPoseidonRound04 TransferPoseidonRound04SemanticData01
theorem column0_checked : checkColumn p copy originalRows parameters 4 before shifted transformed fifthHints ⟨0,by decide⟩=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticChecks01.column0_checked
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticChecks01.column0_checked
theorem column1_checked : checkColumn p copy originalRows parameters 4 before shifted transformed fifthHints ⟨1,by decide⟩=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticChecks01.column1_checked
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticChecks01.column1_checked
theorem column2_checked : checkColumn p copy originalRows parameters 4 before shifted transformed fifthHints ⟨2,by decide⟩=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticChecks01.column2_checked
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticChecks01.column2_checked
theorem column3_checked : checkColumn p copy originalRows parameters 4 before shifted transformed fifthHints ⟨3,by decide⟩=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticChecks01.column3_checked
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticChecks01.column3_checked
theorem column4_checked : checkColumn p copy originalRows parameters 4 before shifted transformed fifthHints ⟨4,by decide⟩=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticChecks01.column4_checked
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticChecks01.column4_checked
theorem column5_checked : checkColumn p copy originalRows parameters 4 before shifted transformed fifthHints ⟨5,by decide⟩=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticChecks01.column5_checked
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticChecks01.column5_checked
theorem mix0_checked : canonical p (after ⟨0,by decide⟩)=canonical p (mixLinear parameters.mds transformed ⟨0,by decide⟩) := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticChecks01.mix0_checked
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticChecks01.mix0_checked
theorem mix1_checked : canonical p (after ⟨1,by decide⟩)=canonical p (mixLinear parameters.mds transformed ⟨1,by decide⟩) := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticChecks01.mix1_checked
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticChecks01.mix1_checked
theorem mix2_checked : canonical p (after ⟨2,by decide⟩)=canonical p (mixLinear parameters.mds transformed ⟨2,by decide⟩) := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticChecks01.mix2_checked
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticChecks01.mix2_checked
theorem mix3_checked : canonical p (after ⟨3,by decide⟩)=canonical p (mixLinear parameters.mds transformed ⟨3,by decide⟩) := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticChecks01.mix3_checked
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticChecks01.mix3_checked
theorem mix4_checked : canonical p (after ⟨4,by decide⟩)=canonical p (mixLinear parameters.mds transformed ⟨4,by decide⟩) := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticChecks01.mix4_checked
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticChecks01.mix4_checked
theorem mix5_checked : canonical p (after ⟨5,by decide⟩)=canonical p (mixLinear parameters.mds transformed ⟨5,by decide⟩) := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticChecks01.mix5_checked
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticChecks01.mix5_checked
end ShielddSecurity.TransferPoseidonRound04SemanticChecks01
