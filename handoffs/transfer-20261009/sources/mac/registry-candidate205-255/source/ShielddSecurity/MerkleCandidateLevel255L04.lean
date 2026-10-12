import ShielddSecurity.CapturedMerkleGlobalLevel185L04
import ShielddSecurity.MerkleArithmeticConstruction253
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleCandidateLevel255L04
open Compiler CompilerAssertionBlock51 CompilerSelectedChunks172
open CapturedInitial73419Generic01 (p copy)
variable {F : Type} [Field F] [CharP F p]
theorem arithmetic (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleGlobalBody181.arithmeticRows 4) := by
 have b0 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L04B00.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L04B00.indices CapturedMerkleGlobalArithmetic184L04B00.rows CapturedMerkleGlobalArithmetic184L04B00.checked
   change ∀ index∈List.range' 4842 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4842 16 (by omega)
 have b1 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L04B01.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L04B01.indices CapturedMerkleGlobalArithmetic184L04B01.rows CapturedMerkleGlobalArithmetic184L04B01.checked
   change ∀ index∈List.range' 4858 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4858 16 (by omega)
 have b2 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L04B02.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L04B02.indices CapturedMerkleGlobalArithmetic184L04B02.rows CapturedMerkleGlobalArithmetic184L04B02.checked
   change ∀ index∈List.range' 4874 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4874 16 (by omega)
 have b3 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L04B03.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L04B03.indices CapturedMerkleGlobalArithmetic184L04B03.rows CapturedMerkleGlobalArithmetic184L04B03.checked
   change ∀ index∈List.range' 4890 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4890 16 (by omega)
 have b4 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L04B04.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L04B04.indices CapturedMerkleGlobalArithmetic184L04B04.rows CapturedMerkleGlobalArithmetic184L04B04.checked
   change ∀ index∈List.range' 4906 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4906 16 (by omega)
 have b5 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L04B05.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L04B05.indices CapturedMerkleGlobalArithmetic184L04B05.rows CapturedMerkleGlobalArithmetic184L04B05.checked
   change ∀ index∈List.range' 4922 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4922 16 (by omega)
 have b6 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L04B06.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L04B06.indices CapturedMerkleGlobalArithmetic184L04B06.rows CapturedMerkleGlobalArithmetic184L04B06.checked
   change ∀ index∈List.range' 4938 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4938 16 (by omega)
 have b7 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L04B07.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L04B07.indices CapturedMerkleGlobalArithmetic184L04B07.rows CapturedMerkleGlobalArithmetic184L04B07.checked
   change ∀ index∈List.range' 4954 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4954 16 (by omega)
 have b8 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L04B08.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L04B08.indices CapturedMerkleGlobalArithmetic184L04B08.rows CapturedMerkleGlobalArithmetic184L04B08.checked
   change ∀ index∈List.range' 4970 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4970 16 (by omega)
 have b9 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L04B09.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L04B09.indices CapturedMerkleGlobalArithmetic184L04B09.rows CapturedMerkleGlobalArithmetic184L04B09.checked
   change ∀ index∈List.range' 4986 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4986 16 (by omega)
 have b10 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L04B10.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L04B10.indices CapturedMerkleGlobalArithmetic184L04B10.rows CapturedMerkleGlobalArithmetic184L04B10.checked
   change ∀ index∈List.range' 5002 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5002 16 (by omega)
 have b11 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L04B11.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L04B11.indices CapturedMerkleGlobalArithmetic184L04B11.rows CapturedMerkleGlobalArithmetic184L04B11.checked
   change ∀ index∈List.range' 5018 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5018 16 (by omega)
 have b12 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L04B12.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L04B12.indices CapturedMerkleGlobalArithmetic184L04B12.rows CapturedMerkleGlobalArithmetic184L04B12.checked
   change ∀ index∈List.range' 5034 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5034 16 (by omega)
 have b13 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L04B13.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L04B13.indices CapturedMerkleGlobalArithmetic184L04B13.rows CapturedMerkleGlobalArithmetic184L04B13.checked
   change ∀ index∈List.range' 5050 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5050 16 (by omega)
 have b14 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L04B14.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L04B14.indices CapturedMerkleGlobalArithmetic184L04B14.rows CapturedMerkleGlobalArithmetic184L04B14.checked
   change ∀ index∈List.range' 5066 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5066 16 (by omega)
 have b15 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L04B15.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L04B15.indices CapturedMerkleGlobalArithmetic184L04B15.rows CapturedMerkleGlobalArithmetic184L04B15.checked
   change ∀ index∈List.range' 5082 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5082 16 (by omega)
 have b16 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L04B16.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L04B16.indices CapturedMerkleGlobalArithmetic184L04B16.rows CapturedMerkleGlobalArithmetic184L04B16.checked
   change ∀ index∈List.range' 5098 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5098 16 (by omega)
 have b17 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L04B17.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L04B17.indices CapturedMerkleGlobalArithmetic184L04B17.rows CapturedMerkleGlobalArithmetic184L04B17.checked
   change ∀ index∈List.range' 5114 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5114 16 (by omega)
 have b18 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L04B18.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L04B18.indices CapturedMerkleGlobalArithmetic184L04B18.rows CapturedMerkleGlobalArithmetic184L04B18.checked
   change ∀ index∈List.range' 5130 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5130 16 (by omega)
 have b19 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L04B19.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L04B19.indices CapturedMerkleGlobalArithmetic184L04B19.rows CapturedMerkleGlobalArithmetic184L04B19.checked
   change ∀ index∈List.range' 5146 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5146 16 (by omega)
 have b20 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L04B20.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L04B20.indices CapturedMerkleGlobalArithmetic184L04B20.rows CapturedMerkleGlobalArithmetic184L04B20.checked
   change ∀ index∈List.range' 5162 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5162 16 (by omega)
 have b21 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L04B21.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L04B21.indices CapturedMerkleGlobalArithmetic184L04B21.rows CapturedMerkleGlobalArithmetic184L04B21.checked
   change ∀ index∈List.range' 5178 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5178 16 (by omega)
 have b22 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L04B22.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L04B22.indices CapturedMerkleGlobalArithmetic184L04B22.rows CapturedMerkleGlobalArithmetic184L04B22.checked
   change ∀ index∈List.range' 5194 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5194 16 (by omega)
 have b23 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L04B23.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L04B23.indices CapturedMerkleGlobalArithmetic184L04B23.rows CapturedMerkleGlobalArithmetic184L04B23.checked
   change ∀ index∈List.range' 5210 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5210 16 (by omega)
 have b24 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L04B24.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L04B24.indices CapturedMerkleGlobalArithmetic184L04B24.rows CapturedMerkleGlobalArithmetic184L04B24.checked
   change ∀ index∈List.range' 5226 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5226 16 (by omega)
 have b25 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L04B25.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L04B25.indices CapturedMerkleGlobalArithmetic184L04B25.rows CapturedMerkleGlobalArithmetic184L04B25.checked
   change ∀ index∈List.range' 5242 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5242 16 (by omega)
 have b26 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L04B26.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L04B26.indices CapturedMerkleGlobalArithmetic184L04B26.rows CapturedMerkleGlobalArithmetic184L04B26.checked
   change ∀ index∈List.range' 5258 8,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5258 8 (by omega)
 rw [←CapturedMerkleGlobalLevel185L04.partition]
 apply flatten_sound
 change AllSatisfied (CapturedFullRelation58.candidate base) [CapturedMerkleGlobalArithmetic184L04B00.rows,CapturedMerkleGlobalArithmetic184L04B01.rows,CapturedMerkleGlobalArithmetic184L04B02.rows,CapturedMerkleGlobalArithmetic184L04B03.rows,CapturedMerkleGlobalArithmetic184L04B04.rows,CapturedMerkleGlobalArithmetic184L04B05.rows,CapturedMerkleGlobalArithmetic184L04B06.rows,CapturedMerkleGlobalArithmetic184L04B07.rows,CapturedMerkleGlobalArithmetic184L04B08.rows,CapturedMerkleGlobalArithmetic184L04B09.rows,CapturedMerkleGlobalArithmetic184L04B10.rows,CapturedMerkleGlobalArithmetic184L04B11.rows,CapturedMerkleGlobalArithmetic184L04B12.rows,CapturedMerkleGlobalArithmetic184L04B13.rows,CapturedMerkleGlobalArithmetic184L04B14.rows,CapturedMerkleGlobalArithmetic184L04B15.rows,CapturedMerkleGlobalArithmetic184L04B16.rows,CapturedMerkleGlobalArithmetic184L04B17.rows,CapturedMerkleGlobalArithmetic184L04B18.rows,CapturedMerkleGlobalArithmetic184L04B19.rows,CapturedMerkleGlobalArithmetic184L04B20.rows,CapturedMerkleGlobalArithmetic184L04B21.rows,CapturedMerkleGlobalArithmetic184L04B22.rows,CapturedMerkleGlobalArithmetic184L04B23.rows,CapturedMerkleGlobalArithmetic184L04B24.rows,CapturedMerkleGlobalArithmetic184L04B25.rows,CapturedMerkleGlobalArithmetic184L04B26.rows]
 exact ⟨b0,⟨b1,⟨b2,⟨b3,⟨b4,⟨b5,⟨b6,⟨b7,⟨b8,⟨b9,⟨b10,⟨b11,⟨b12,⟨b13,⟨b14,⟨b15,⟨b16,⟨b17,⟨b18,⟨b19,⟨b20,⟨b21,⟨b22,⟨b23,⟨b24,⟨b25,⟨b26,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleFamily32Whole.rows (F:=F) 4) :=
 MerkleArithmeticConstruction253.body_rows base 4 CapturedMerkleGlobalLevel185L04.copy_checked (arithmetic base)
end ShielddSecurity.MerkleCandidateLevel255L04

set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L04.arithmetic
#print axioms ShielddSecurity.MerkleCandidateLevel255L04.arithmetic
set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L04.rows
#print axioms ShielddSecurity.MerkleCandidateLevel255L04.rows
