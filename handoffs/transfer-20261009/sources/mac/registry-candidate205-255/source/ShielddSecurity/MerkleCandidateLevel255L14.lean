import ShielddSecurity.CapturedMerkleGlobalLevel185L14
import ShielddSecurity.MerkleArithmeticConstruction253
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleCandidateLevel255L14
open Compiler CompilerAssertionBlock51 CompilerSelectedChunks172
open CapturedInitial73419Generic01 (p copy)
variable {F : Type} [Field F] [CharP F p]
theorem arithmetic (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleGlobalBody181.arithmeticRows 14) := by
 have b0 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L14B00.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L14B00.indices CapturedMerkleGlobalArithmetic184L14B00.rows CapturedMerkleGlobalArithmetic184L14B00.checked
   change ∀ index∈List.range' 9082 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9082 16 (by omega)
 have b1 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L14B01.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L14B01.indices CapturedMerkleGlobalArithmetic184L14B01.rows CapturedMerkleGlobalArithmetic184L14B01.checked
   change ∀ index∈List.range' 9098 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9098 16 (by omega)
 have b2 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L14B02.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L14B02.indices CapturedMerkleGlobalArithmetic184L14B02.rows CapturedMerkleGlobalArithmetic184L14B02.checked
   change ∀ index∈List.range' 9114 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9114 16 (by omega)
 have b3 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L14B03.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L14B03.indices CapturedMerkleGlobalArithmetic184L14B03.rows CapturedMerkleGlobalArithmetic184L14B03.checked
   change ∀ index∈List.range' 9130 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9130 16 (by omega)
 have b4 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L14B04.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L14B04.indices CapturedMerkleGlobalArithmetic184L14B04.rows CapturedMerkleGlobalArithmetic184L14B04.checked
   change ∀ index∈List.range' 9146 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9146 16 (by omega)
 have b5 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L14B05.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L14B05.indices CapturedMerkleGlobalArithmetic184L14B05.rows CapturedMerkleGlobalArithmetic184L14B05.checked
   change ∀ index∈List.range' 9162 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9162 16 (by omega)
 have b6 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L14B06.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L14B06.indices CapturedMerkleGlobalArithmetic184L14B06.rows CapturedMerkleGlobalArithmetic184L14B06.checked
   change ∀ index∈List.range' 9178 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9178 16 (by omega)
 have b7 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L14B07.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L14B07.indices CapturedMerkleGlobalArithmetic184L14B07.rows CapturedMerkleGlobalArithmetic184L14B07.checked
   change ∀ index∈List.range' 9194 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9194 16 (by omega)
 have b8 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L14B08.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L14B08.indices CapturedMerkleGlobalArithmetic184L14B08.rows CapturedMerkleGlobalArithmetic184L14B08.checked
   change ∀ index∈List.range' 9210 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9210 16 (by omega)
 have b9 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L14B09.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L14B09.indices CapturedMerkleGlobalArithmetic184L14B09.rows CapturedMerkleGlobalArithmetic184L14B09.checked
   change ∀ index∈List.range' 9226 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9226 16 (by omega)
 have b10 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L14B10.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L14B10.indices CapturedMerkleGlobalArithmetic184L14B10.rows CapturedMerkleGlobalArithmetic184L14B10.checked
   change ∀ index∈List.range' 9242 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9242 16 (by omega)
 have b11 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L14B11.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L14B11.indices CapturedMerkleGlobalArithmetic184L14B11.rows CapturedMerkleGlobalArithmetic184L14B11.checked
   change ∀ index∈List.range' 9258 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9258 16 (by omega)
 have b12 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L14B12.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L14B12.indices CapturedMerkleGlobalArithmetic184L14B12.rows CapturedMerkleGlobalArithmetic184L14B12.checked
   change ∀ index∈List.range' 9274 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9274 16 (by omega)
 have b13 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L14B13.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L14B13.indices CapturedMerkleGlobalArithmetic184L14B13.rows CapturedMerkleGlobalArithmetic184L14B13.checked
   change ∀ index∈List.range' 9290 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9290 16 (by omega)
 have b14 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L14B14.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L14B14.indices CapturedMerkleGlobalArithmetic184L14B14.rows CapturedMerkleGlobalArithmetic184L14B14.checked
   change ∀ index∈List.range' 9306 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9306 16 (by omega)
 have b15 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L14B15.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L14B15.indices CapturedMerkleGlobalArithmetic184L14B15.rows CapturedMerkleGlobalArithmetic184L14B15.checked
   change ∀ index∈List.range' 9322 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9322 16 (by omega)
 have b16 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L14B16.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L14B16.indices CapturedMerkleGlobalArithmetic184L14B16.rows CapturedMerkleGlobalArithmetic184L14B16.checked
   change ∀ index∈List.range' 9338 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9338 16 (by omega)
 have b17 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L14B17.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L14B17.indices CapturedMerkleGlobalArithmetic184L14B17.rows CapturedMerkleGlobalArithmetic184L14B17.checked
   change ∀ index∈List.range' 9354 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9354 16 (by omega)
 have b18 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L14B18.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L14B18.indices CapturedMerkleGlobalArithmetic184L14B18.rows CapturedMerkleGlobalArithmetic184L14B18.checked
   change ∀ index∈List.range' 9370 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9370 16 (by omega)
 have b19 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L14B19.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L14B19.indices CapturedMerkleGlobalArithmetic184L14B19.rows CapturedMerkleGlobalArithmetic184L14B19.checked
   change ∀ index∈List.range' 9386 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9386 16 (by omega)
 have b20 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L14B20.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L14B20.indices CapturedMerkleGlobalArithmetic184L14B20.rows CapturedMerkleGlobalArithmetic184L14B20.checked
   change ∀ index∈List.range' 9402 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9402 16 (by omega)
 have b21 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L14B21.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L14B21.indices CapturedMerkleGlobalArithmetic184L14B21.rows CapturedMerkleGlobalArithmetic184L14B21.checked
   change ∀ index∈List.range' 9418 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9418 16 (by omega)
 have b22 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L14B22.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L14B22.indices CapturedMerkleGlobalArithmetic184L14B22.rows CapturedMerkleGlobalArithmetic184L14B22.checked
   change ∀ index∈List.range' 9434 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9434 16 (by omega)
 have b23 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L14B23.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L14B23.indices CapturedMerkleGlobalArithmetic184L14B23.rows CapturedMerkleGlobalArithmetic184L14B23.checked
   change ∀ index∈List.range' 9450 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9450 16 (by omega)
 have b24 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L14B24.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L14B24.indices CapturedMerkleGlobalArithmetic184L14B24.rows CapturedMerkleGlobalArithmetic184L14B24.checked
   change ∀ index∈List.range' 9466 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9466 16 (by omega)
 have b25 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L14B25.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L14B25.indices CapturedMerkleGlobalArithmetic184L14B25.rows CapturedMerkleGlobalArithmetic184L14B25.checked
   change ∀ index∈List.range' 9482 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9482 16 (by omega)
 have b26 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L14B26.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L14B26.indices CapturedMerkleGlobalArithmetic184L14B26.rows CapturedMerkleGlobalArithmetic184L14B26.checked
   change ∀ index∈List.range' 9498 8,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9498 8 (by omega)
 rw [←CapturedMerkleGlobalLevel185L14.partition]
 apply flatten_sound
 change AllSatisfied (CapturedFullRelation58.candidate base) [CapturedMerkleGlobalArithmetic184L14B00.rows,CapturedMerkleGlobalArithmetic184L14B01.rows,CapturedMerkleGlobalArithmetic184L14B02.rows,CapturedMerkleGlobalArithmetic184L14B03.rows,CapturedMerkleGlobalArithmetic184L14B04.rows,CapturedMerkleGlobalArithmetic184L14B05.rows,CapturedMerkleGlobalArithmetic184L14B06.rows,CapturedMerkleGlobalArithmetic184L14B07.rows,CapturedMerkleGlobalArithmetic184L14B08.rows,CapturedMerkleGlobalArithmetic184L14B09.rows,CapturedMerkleGlobalArithmetic184L14B10.rows,CapturedMerkleGlobalArithmetic184L14B11.rows,CapturedMerkleGlobalArithmetic184L14B12.rows,CapturedMerkleGlobalArithmetic184L14B13.rows,CapturedMerkleGlobalArithmetic184L14B14.rows,CapturedMerkleGlobalArithmetic184L14B15.rows,CapturedMerkleGlobalArithmetic184L14B16.rows,CapturedMerkleGlobalArithmetic184L14B17.rows,CapturedMerkleGlobalArithmetic184L14B18.rows,CapturedMerkleGlobalArithmetic184L14B19.rows,CapturedMerkleGlobalArithmetic184L14B20.rows,CapturedMerkleGlobalArithmetic184L14B21.rows,CapturedMerkleGlobalArithmetic184L14B22.rows,CapturedMerkleGlobalArithmetic184L14B23.rows,CapturedMerkleGlobalArithmetic184L14B24.rows,CapturedMerkleGlobalArithmetic184L14B25.rows,CapturedMerkleGlobalArithmetic184L14B26.rows]
 exact ⟨b0,⟨b1,⟨b2,⟨b3,⟨b4,⟨b5,⟨b6,⟨b7,⟨b8,⟨b9,⟨b10,⟨b11,⟨b12,⟨b13,⟨b14,⟨b15,⟨b16,⟨b17,⟨b18,⟨b19,⟨b20,⟨b21,⟨b22,⟨b23,⟨b24,⟨b25,⟨b26,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleFamily32Whole.rows (F:=F) 14) :=
 MerkleArithmeticConstruction253.body_rows base 14 CapturedMerkleGlobalLevel185L14.copy_checked (arithmetic base)
end ShielddSecurity.MerkleCandidateLevel255L14

set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L14.arithmetic
#print axioms ShielddSecurity.MerkleCandidateLevel255L14.arithmetic
set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L14.rows
#print axioms ShielddSecurity.MerkleCandidateLevel255L14.rows
