import ShielddSecurity.CapturedMerkleGlobalLevel185L11
import ShielddSecurity.MerkleArithmeticConstruction253
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleCandidateLevel255L11
open Compiler CompilerAssertionBlock51 CompilerSelectedChunks172
open CapturedInitial73419Generic01 (p copy)
variable {F : Type} [Field F] [CharP F p]
theorem arithmetic (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleGlobalBody181.arithmeticRows 11) := by
 have b0 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L11B00.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L11B00.indices CapturedMerkleGlobalArithmetic184L11B00.rows CapturedMerkleGlobalArithmetic184L11B00.checked
   change ∀ index∈List.range' 7810 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7810 16 (by omega)
 have b1 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L11B01.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L11B01.indices CapturedMerkleGlobalArithmetic184L11B01.rows CapturedMerkleGlobalArithmetic184L11B01.checked
   change ∀ index∈List.range' 7826 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7826 16 (by omega)
 have b2 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L11B02.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L11B02.indices CapturedMerkleGlobalArithmetic184L11B02.rows CapturedMerkleGlobalArithmetic184L11B02.checked
   change ∀ index∈List.range' 7842 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7842 16 (by omega)
 have b3 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L11B03.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L11B03.indices CapturedMerkleGlobalArithmetic184L11B03.rows CapturedMerkleGlobalArithmetic184L11B03.checked
   change ∀ index∈List.range' 7858 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7858 16 (by omega)
 have b4 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L11B04.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L11B04.indices CapturedMerkleGlobalArithmetic184L11B04.rows CapturedMerkleGlobalArithmetic184L11B04.checked
   change ∀ index∈List.range' 7874 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7874 16 (by omega)
 have b5 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L11B05.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L11B05.indices CapturedMerkleGlobalArithmetic184L11B05.rows CapturedMerkleGlobalArithmetic184L11B05.checked
   change ∀ index∈List.range' 7890 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7890 16 (by omega)
 have b6 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L11B06.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L11B06.indices CapturedMerkleGlobalArithmetic184L11B06.rows CapturedMerkleGlobalArithmetic184L11B06.checked
   change ∀ index∈List.range' 7906 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7906 16 (by omega)
 have b7 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L11B07.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L11B07.indices CapturedMerkleGlobalArithmetic184L11B07.rows CapturedMerkleGlobalArithmetic184L11B07.checked
   change ∀ index∈List.range' 7922 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7922 16 (by omega)
 have b8 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L11B08.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L11B08.indices CapturedMerkleGlobalArithmetic184L11B08.rows CapturedMerkleGlobalArithmetic184L11B08.checked
   change ∀ index∈List.range' 7938 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7938 16 (by omega)
 have b9 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L11B09.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L11B09.indices CapturedMerkleGlobalArithmetic184L11B09.rows CapturedMerkleGlobalArithmetic184L11B09.checked
   change ∀ index∈List.range' 7954 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7954 16 (by omega)
 have b10 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L11B10.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L11B10.indices CapturedMerkleGlobalArithmetic184L11B10.rows CapturedMerkleGlobalArithmetic184L11B10.checked
   change ∀ index∈List.range' 7970 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7970 16 (by omega)
 have b11 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L11B11.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L11B11.indices CapturedMerkleGlobalArithmetic184L11B11.rows CapturedMerkleGlobalArithmetic184L11B11.checked
   change ∀ index∈List.range' 7986 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7986 16 (by omega)
 have b12 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L11B12.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L11B12.indices CapturedMerkleGlobalArithmetic184L11B12.rows CapturedMerkleGlobalArithmetic184L11B12.checked
   change ∀ index∈List.range' 8002 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8002 16 (by omega)
 have b13 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L11B13.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L11B13.indices CapturedMerkleGlobalArithmetic184L11B13.rows CapturedMerkleGlobalArithmetic184L11B13.checked
   change ∀ index∈List.range' 8018 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8018 16 (by omega)
 have b14 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L11B14.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L11B14.indices CapturedMerkleGlobalArithmetic184L11B14.rows CapturedMerkleGlobalArithmetic184L11B14.checked
   change ∀ index∈List.range' 8034 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8034 16 (by omega)
 have b15 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L11B15.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L11B15.indices CapturedMerkleGlobalArithmetic184L11B15.rows CapturedMerkleGlobalArithmetic184L11B15.checked
   change ∀ index∈List.range' 8050 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8050 16 (by omega)
 have b16 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L11B16.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L11B16.indices CapturedMerkleGlobalArithmetic184L11B16.rows CapturedMerkleGlobalArithmetic184L11B16.checked
   change ∀ index∈List.range' 8066 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8066 16 (by omega)
 have b17 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L11B17.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L11B17.indices CapturedMerkleGlobalArithmetic184L11B17.rows CapturedMerkleGlobalArithmetic184L11B17.checked
   change ∀ index∈List.range' 8082 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8082 16 (by omega)
 have b18 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L11B18.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L11B18.indices CapturedMerkleGlobalArithmetic184L11B18.rows CapturedMerkleGlobalArithmetic184L11B18.checked
   change ∀ index∈List.range' 8098 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8098 16 (by omega)
 have b19 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L11B19.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L11B19.indices CapturedMerkleGlobalArithmetic184L11B19.rows CapturedMerkleGlobalArithmetic184L11B19.checked
   change ∀ index∈List.range' 8114 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8114 16 (by omega)
 have b20 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L11B20.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L11B20.indices CapturedMerkleGlobalArithmetic184L11B20.rows CapturedMerkleGlobalArithmetic184L11B20.checked
   change ∀ index∈List.range' 8130 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8130 16 (by omega)
 have b21 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L11B21.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L11B21.indices CapturedMerkleGlobalArithmetic184L11B21.rows CapturedMerkleGlobalArithmetic184L11B21.checked
   change ∀ index∈List.range' 8146 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8146 16 (by omega)
 have b22 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L11B22.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L11B22.indices CapturedMerkleGlobalArithmetic184L11B22.rows CapturedMerkleGlobalArithmetic184L11B22.checked
   change ∀ index∈List.range' 8162 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8162 16 (by omega)
 have b23 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L11B23.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L11B23.indices CapturedMerkleGlobalArithmetic184L11B23.rows CapturedMerkleGlobalArithmetic184L11B23.checked
   change ∀ index∈List.range' 8178 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8178 16 (by omega)
 have b24 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L11B24.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L11B24.indices CapturedMerkleGlobalArithmetic184L11B24.rows CapturedMerkleGlobalArithmetic184L11B24.checked
   change ∀ index∈List.range' 8194 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8194 16 (by omega)
 have b25 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L11B25.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L11B25.indices CapturedMerkleGlobalArithmetic184L11B25.rows CapturedMerkleGlobalArithmetic184L11B25.checked
   change ∀ index∈List.range' 8210 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8210 16 (by omega)
 have b26 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L11B26.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L11B26.indices CapturedMerkleGlobalArithmetic184L11B26.rows CapturedMerkleGlobalArithmetic184L11B26.checked
   change ∀ index∈List.range' 8226 8,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8226 8 (by omega)
 rw [←CapturedMerkleGlobalLevel185L11.partition]
 apply flatten_sound
 change AllSatisfied (CapturedFullRelation58.candidate base) [CapturedMerkleGlobalArithmetic184L11B00.rows,CapturedMerkleGlobalArithmetic184L11B01.rows,CapturedMerkleGlobalArithmetic184L11B02.rows,CapturedMerkleGlobalArithmetic184L11B03.rows,CapturedMerkleGlobalArithmetic184L11B04.rows,CapturedMerkleGlobalArithmetic184L11B05.rows,CapturedMerkleGlobalArithmetic184L11B06.rows,CapturedMerkleGlobalArithmetic184L11B07.rows,CapturedMerkleGlobalArithmetic184L11B08.rows,CapturedMerkleGlobalArithmetic184L11B09.rows,CapturedMerkleGlobalArithmetic184L11B10.rows,CapturedMerkleGlobalArithmetic184L11B11.rows,CapturedMerkleGlobalArithmetic184L11B12.rows,CapturedMerkleGlobalArithmetic184L11B13.rows,CapturedMerkleGlobalArithmetic184L11B14.rows,CapturedMerkleGlobalArithmetic184L11B15.rows,CapturedMerkleGlobalArithmetic184L11B16.rows,CapturedMerkleGlobalArithmetic184L11B17.rows,CapturedMerkleGlobalArithmetic184L11B18.rows,CapturedMerkleGlobalArithmetic184L11B19.rows,CapturedMerkleGlobalArithmetic184L11B20.rows,CapturedMerkleGlobalArithmetic184L11B21.rows,CapturedMerkleGlobalArithmetic184L11B22.rows,CapturedMerkleGlobalArithmetic184L11B23.rows,CapturedMerkleGlobalArithmetic184L11B24.rows,CapturedMerkleGlobalArithmetic184L11B25.rows,CapturedMerkleGlobalArithmetic184L11B26.rows]
 exact ⟨b0,⟨b1,⟨b2,⟨b3,⟨b4,⟨b5,⟨b6,⟨b7,⟨b8,⟨b9,⟨b10,⟨b11,⟨b12,⟨b13,⟨b14,⟨b15,⟨b16,⟨b17,⟨b18,⟨b19,⟨b20,⟨b21,⟨b22,⟨b23,⟨b24,⟨b25,⟨b26,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleFamily32Whole.rows (F:=F) 11) :=
 MerkleArithmeticConstruction253.body_rows base 11 CapturedMerkleGlobalLevel185L11.copy_checked (arithmetic base)
end ShielddSecurity.MerkleCandidateLevel255L11

set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L11.arithmetic
#print axioms ShielddSecurity.MerkleCandidateLevel255L11.arithmetic
set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L11.rows
#print axioms ShielddSecurity.MerkleCandidateLevel255L11.rows
