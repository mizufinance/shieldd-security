import ShielddSecurity.CapturedMerkleGlobalLevel185L00
import ShielddSecurity.MerkleArithmeticConstruction253
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleCandidateLevel255L00
open Compiler CompilerAssertionBlock51 CompilerSelectedChunks172
open CapturedInitial73419Generic01 (p copy)
variable {F : Type} [Field F] [CharP F p]
theorem arithmetic (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleGlobalBody181.arithmeticRows 0) := by
 have b0 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalPilot182.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalPilot182.indices CapturedMerkleGlobalPilot182.rows CapturedMerkleGlobalPilot182.checked
   change ∀ index∈List.range' 3146 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3146 16 (by omega)
 have b1 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L00B01.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L00B01.indices CapturedMerkleGlobalArithmetic184L00B01.rows CapturedMerkleGlobalArithmetic184L00B01.checked
   change ∀ index∈List.range' 3162 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3162 16 (by omega)
 have b2 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L00B02.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L00B02.indices CapturedMerkleGlobalArithmetic184L00B02.rows CapturedMerkleGlobalArithmetic184L00B02.checked
   change ∀ index∈List.range' 3178 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3178 16 (by omega)
 have b3 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L00B03.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L00B03.indices CapturedMerkleGlobalArithmetic184L00B03.rows CapturedMerkleGlobalArithmetic184L00B03.checked
   change ∀ index∈List.range' 3194 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3194 16 (by omega)
 have b4 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L00B04.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L00B04.indices CapturedMerkleGlobalArithmetic184L00B04.rows CapturedMerkleGlobalArithmetic184L00B04.checked
   change ∀ index∈List.range' 3210 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3210 16 (by omega)
 have b5 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L00B05.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L00B05.indices CapturedMerkleGlobalArithmetic184L00B05.rows CapturedMerkleGlobalArithmetic184L00B05.checked
   change ∀ index∈List.range' 3226 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3226 16 (by omega)
 have b6 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L00B06.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L00B06.indices CapturedMerkleGlobalArithmetic184L00B06.rows CapturedMerkleGlobalArithmetic184L00B06.checked
   change ∀ index∈List.range' 3242 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3242 16 (by omega)
 have b7 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L00B07.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L00B07.indices CapturedMerkleGlobalArithmetic184L00B07.rows CapturedMerkleGlobalArithmetic184L00B07.checked
   change ∀ index∈List.range' 3258 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3258 16 (by omega)
 have b8 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L00B08.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L00B08.indices CapturedMerkleGlobalArithmetic184L00B08.rows CapturedMerkleGlobalArithmetic184L00B08.checked
   change ∀ index∈List.range' 3274 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3274 16 (by omega)
 have b9 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L00B09.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L00B09.indices CapturedMerkleGlobalArithmetic184L00B09.rows CapturedMerkleGlobalArithmetic184L00B09.checked
   change ∀ index∈List.range' 3290 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3290 16 (by omega)
 have b10 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L00B10.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L00B10.indices CapturedMerkleGlobalArithmetic184L00B10.rows CapturedMerkleGlobalArithmetic184L00B10.checked
   change ∀ index∈List.range' 3306 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3306 16 (by omega)
 have b11 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L00B11.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L00B11.indices CapturedMerkleGlobalArithmetic184L00B11.rows CapturedMerkleGlobalArithmetic184L00B11.checked
   change ∀ index∈List.range' 3322 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3322 16 (by omega)
 have b12 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L00B12.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L00B12.indices CapturedMerkleGlobalArithmetic184L00B12.rows CapturedMerkleGlobalArithmetic184L00B12.checked
   change ∀ index∈List.range' 3338 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3338 16 (by omega)
 have b13 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L00B13.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L00B13.indices CapturedMerkleGlobalArithmetic184L00B13.rows CapturedMerkleGlobalArithmetic184L00B13.checked
   change ∀ index∈List.range' 3354 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3354 16 (by omega)
 have b14 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L00B14.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L00B14.indices CapturedMerkleGlobalArithmetic184L00B14.rows CapturedMerkleGlobalArithmetic184L00B14.checked
   change ∀ index∈List.range' 3370 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3370 16 (by omega)
 have b15 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L00B15.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L00B15.indices CapturedMerkleGlobalArithmetic184L00B15.rows CapturedMerkleGlobalArithmetic184L00B15.checked
   change ∀ index∈List.range' 3386 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3386 16 (by omega)
 have b16 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L00B16.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L00B16.indices CapturedMerkleGlobalArithmetic184L00B16.rows CapturedMerkleGlobalArithmetic184L00B16.checked
   change ∀ index∈List.range' 3402 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3402 16 (by omega)
 have b17 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L00B17.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L00B17.indices CapturedMerkleGlobalArithmetic184L00B17.rows CapturedMerkleGlobalArithmetic184L00B17.checked
   change ∀ index∈List.range' 3418 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3418 16 (by omega)
 have b18 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L00B18.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L00B18.indices CapturedMerkleGlobalArithmetic184L00B18.rows CapturedMerkleGlobalArithmetic184L00B18.checked
   change ∀ index∈List.range' 3434 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3434 16 (by omega)
 have b19 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L00B19.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L00B19.indices CapturedMerkleGlobalArithmetic184L00B19.rows CapturedMerkleGlobalArithmetic184L00B19.checked
   change ∀ index∈List.range' 3450 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3450 16 (by omega)
 have b20 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L00B20.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L00B20.indices CapturedMerkleGlobalArithmetic184L00B20.rows CapturedMerkleGlobalArithmetic184L00B20.checked
   change ∀ index∈List.range' 3466 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3466 16 (by omega)
 have b21 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L00B21.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L00B21.indices CapturedMerkleGlobalArithmetic184L00B21.rows CapturedMerkleGlobalArithmetic184L00B21.checked
   change ∀ index∈List.range' 3482 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3482 16 (by omega)
 have b22 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L00B22.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L00B22.indices CapturedMerkleGlobalArithmetic184L00B22.rows CapturedMerkleGlobalArithmetic184L00B22.checked
   change ∀ index∈List.range' 3498 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3498 16 (by omega)
 have b23 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L00B23.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L00B23.indices CapturedMerkleGlobalArithmetic184L00B23.rows CapturedMerkleGlobalArithmetic184L00B23.checked
   change ∀ index∈List.range' 3514 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3514 16 (by omega)
 have b24 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L00B24.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L00B24.indices CapturedMerkleGlobalArithmetic184L00B24.rows CapturedMerkleGlobalArithmetic184L00B24.checked
   change ∀ index∈List.range' 3530 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3530 16 (by omega)
 have b25 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L00B25.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L00B25.indices CapturedMerkleGlobalArithmetic184L00B25.rows CapturedMerkleGlobalArithmetic184L00B25.checked
   change ∀ index∈List.range' 3546 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3546 16 (by omega)
 have b26 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L00B26.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L00B26.indices CapturedMerkleGlobalArithmetic184L00B26.rows CapturedMerkleGlobalArithmetic184L00B26.checked
   change ∀ index∈List.range' 3562 8,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3562 8 (by omega)
 rw [←CapturedMerkleGlobalLevel185L00.partition]
 apply flatten_sound
 change AllSatisfied (CapturedFullRelation58.candidate base) [CapturedMerkleGlobalPilot182.rows,CapturedMerkleGlobalArithmetic184L00B01.rows,CapturedMerkleGlobalArithmetic184L00B02.rows,CapturedMerkleGlobalArithmetic184L00B03.rows,CapturedMerkleGlobalArithmetic184L00B04.rows,CapturedMerkleGlobalArithmetic184L00B05.rows,CapturedMerkleGlobalArithmetic184L00B06.rows,CapturedMerkleGlobalArithmetic184L00B07.rows,CapturedMerkleGlobalArithmetic184L00B08.rows,CapturedMerkleGlobalArithmetic184L00B09.rows,CapturedMerkleGlobalArithmetic184L00B10.rows,CapturedMerkleGlobalArithmetic184L00B11.rows,CapturedMerkleGlobalArithmetic184L00B12.rows,CapturedMerkleGlobalArithmetic184L00B13.rows,CapturedMerkleGlobalArithmetic184L00B14.rows,CapturedMerkleGlobalArithmetic184L00B15.rows,CapturedMerkleGlobalArithmetic184L00B16.rows,CapturedMerkleGlobalArithmetic184L00B17.rows,CapturedMerkleGlobalArithmetic184L00B18.rows,CapturedMerkleGlobalArithmetic184L00B19.rows,CapturedMerkleGlobalArithmetic184L00B20.rows,CapturedMerkleGlobalArithmetic184L00B21.rows,CapturedMerkleGlobalArithmetic184L00B22.rows,CapturedMerkleGlobalArithmetic184L00B23.rows,CapturedMerkleGlobalArithmetic184L00B24.rows,CapturedMerkleGlobalArithmetic184L00B25.rows,CapturedMerkleGlobalArithmetic184L00B26.rows]
 exact ⟨b0,⟨b1,⟨b2,⟨b3,⟨b4,⟨b5,⟨b6,⟨b7,⟨b8,⟨b9,⟨b10,⟨b11,⟨b12,⟨b13,⟨b14,⟨b15,⟨b16,⟨b17,⟨b18,⟨b19,⟨b20,⟨b21,⟨b22,⟨b23,⟨b24,⟨b25,⟨b26,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleFamily32Whole.rows (F:=F) 0) :=
 MerkleArithmeticConstruction253.body_rows base 0 CapturedMerkleGlobalLevel185L00.copy_checked (arithmetic base)
end ShielddSecurity.MerkleCandidateLevel255L00

set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L00.arithmetic
#print axioms ShielddSecurity.MerkleCandidateLevel255L00.arithmetic
set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L00.rows
#print axioms ShielddSecurity.MerkleCandidateLevel255L00.rows
