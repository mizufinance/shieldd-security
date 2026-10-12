import ShielddSecurity.CapturedMerkleGlobalLevel185L07
import ShielddSecurity.MerkleArithmeticConstruction253
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleCandidateLevel255L07
open Compiler CompilerAssertionBlock51 CompilerSelectedChunks172
open CapturedInitial73419Generic01 (p copy)
variable {F : Type} [Field F] [CharP F p]
theorem arithmetic (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleGlobalBody181.arithmeticRows 7) := by
 have b0 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L07B00.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L07B00.indices CapturedMerkleGlobalArithmetic184L07B00.rows CapturedMerkleGlobalArithmetic184L07B00.checked
   change ∀ index∈List.range' 6114 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6114 16 (by omega)
 have b1 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L07B01.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L07B01.indices CapturedMerkleGlobalArithmetic184L07B01.rows CapturedMerkleGlobalArithmetic184L07B01.checked
   change ∀ index∈List.range' 6130 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6130 16 (by omega)
 have b2 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L07B02.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L07B02.indices CapturedMerkleGlobalArithmetic184L07B02.rows CapturedMerkleGlobalArithmetic184L07B02.checked
   change ∀ index∈List.range' 6146 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6146 16 (by omega)
 have b3 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L07B03.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L07B03.indices CapturedMerkleGlobalArithmetic184L07B03.rows CapturedMerkleGlobalArithmetic184L07B03.checked
   change ∀ index∈List.range' 6162 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6162 16 (by omega)
 have b4 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L07B04.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L07B04.indices CapturedMerkleGlobalArithmetic184L07B04.rows CapturedMerkleGlobalArithmetic184L07B04.checked
   change ∀ index∈List.range' 6178 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6178 16 (by omega)
 have b5 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L07B05.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L07B05.indices CapturedMerkleGlobalArithmetic184L07B05.rows CapturedMerkleGlobalArithmetic184L07B05.checked
   change ∀ index∈List.range' 6194 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6194 16 (by omega)
 have b6 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L07B06.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L07B06.indices CapturedMerkleGlobalArithmetic184L07B06.rows CapturedMerkleGlobalArithmetic184L07B06.checked
   change ∀ index∈List.range' 6210 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6210 16 (by omega)
 have b7 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L07B07.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L07B07.indices CapturedMerkleGlobalArithmetic184L07B07.rows CapturedMerkleGlobalArithmetic184L07B07.checked
   change ∀ index∈List.range' 6226 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6226 16 (by omega)
 have b8 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L07B08.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L07B08.indices CapturedMerkleGlobalArithmetic184L07B08.rows CapturedMerkleGlobalArithmetic184L07B08.checked
   change ∀ index∈List.range' 6242 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6242 16 (by omega)
 have b9 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L07B09.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L07B09.indices CapturedMerkleGlobalArithmetic184L07B09.rows CapturedMerkleGlobalArithmetic184L07B09.checked
   change ∀ index∈List.range' 6258 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6258 16 (by omega)
 have b10 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L07B10.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L07B10.indices CapturedMerkleGlobalArithmetic184L07B10.rows CapturedMerkleGlobalArithmetic184L07B10.checked
   change ∀ index∈List.range' 6274 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6274 16 (by omega)
 have b11 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L07B11.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L07B11.indices CapturedMerkleGlobalArithmetic184L07B11.rows CapturedMerkleGlobalArithmetic184L07B11.checked
   change ∀ index∈List.range' 6290 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6290 16 (by omega)
 have b12 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L07B12.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L07B12.indices CapturedMerkleGlobalArithmetic184L07B12.rows CapturedMerkleGlobalArithmetic184L07B12.checked
   change ∀ index∈List.range' 6306 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6306 16 (by omega)
 have b13 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L07B13.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L07B13.indices CapturedMerkleGlobalArithmetic184L07B13.rows CapturedMerkleGlobalArithmetic184L07B13.checked
   change ∀ index∈List.range' 6322 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6322 16 (by omega)
 have b14 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L07B14.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L07B14.indices CapturedMerkleGlobalArithmetic184L07B14.rows CapturedMerkleGlobalArithmetic184L07B14.checked
   change ∀ index∈List.range' 6338 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6338 16 (by omega)
 have b15 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L07B15.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L07B15.indices CapturedMerkleGlobalArithmetic184L07B15.rows CapturedMerkleGlobalArithmetic184L07B15.checked
   change ∀ index∈List.range' 6354 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6354 16 (by omega)
 have b16 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L07B16.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L07B16.indices CapturedMerkleGlobalArithmetic184L07B16.rows CapturedMerkleGlobalArithmetic184L07B16.checked
   change ∀ index∈List.range' 6370 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6370 16 (by omega)
 have b17 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L07B17.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L07B17.indices CapturedMerkleGlobalArithmetic184L07B17.rows CapturedMerkleGlobalArithmetic184L07B17.checked
   change ∀ index∈List.range' 6386 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6386 16 (by omega)
 have b18 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L07B18.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L07B18.indices CapturedMerkleGlobalArithmetic184L07B18.rows CapturedMerkleGlobalArithmetic184L07B18.checked
   change ∀ index∈List.range' 6402 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6402 16 (by omega)
 have b19 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L07B19.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L07B19.indices CapturedMerkleGlobalArithmetic184L07B19.rows CapturedMerkleGlobalArithmetic184L07B19.checked
   change ∀ index∈List.range' 6418 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6418 16 (by omega)
 have b20 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L07B20.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L07B20.indices CapturedMerkleGlobalArithmetic184L07B20.rows CapturedMerkleGlobalArithmetic184L07B20.checked
   change ∀ index∈List.range' 6434 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6434 16 (by omega)
 have b21 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L07B21.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L07B21.indices CapturedMerkleGlobalArithmetic184L07B21.rows CapturedMerkleGlobalArithmetic184L07B21.checked
   change ∀ index∈List.range' 6450 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6450 16 (by omega)
 have b22 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L07B22.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L07B22.indices CapturedMerkleGlobalArithmetic184L07B22.rows CapturedMerkleGlobalArithmetic184L07B22.checked
   change ∀ index∈List.range' 6466 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6466 16 (by omega)
 have b23 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L07B23.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L07B23.indices CapturedMerkleGlobalArithmetic184L07B23.rows CapturedMerkleGlobalArithmetic184L07B23.checked
   change ∀ index∈List.range' 6482 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6482 16 (by omega)
 have b24 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L07B24.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L07B24.indices CapturedMerkleGlobalArithmetic184L07B24.rows CapturedMerkleGlobalArithmetic184L07B24.checked
   change ∀ index∈List.range' 6498 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6498 16 (by omega)
 have b25 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L07B25.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L07B25.indices CapturedMerkleGlobalArithmetic184L07B25.rows CapturedMerkleGlobalArithmetic184L07B25.checked
   change ∀ index∈List.range' 6514 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6514 16 (by omega)
 have b26 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L07B26.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L07B26.indices CapturedMerkleGlobalArithmetic184L07B26.rows CapturedMerkleGlobalArithmetic184L07B26.checked
   change ∀ index∈List.range' 6530 8,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6530 8 (by omega)
 rw [←CapturedMerkleGlobalLevel185L07.partition]
 apply flatten_sound
 change AllSatisfied (CapturedFullRelation58.candidate base) [CapturedMerkleGlobalArithmetic184L07B00.rows,CapturedMerkleGlobalArithmetic184L07B01.rows,CapturedMerkleGlobalArithmetic184L07B02.rows,CapturedMerkleGlobalArithmetic184L07B03.rows,CapturedMerkleGlobalArithmetic184L07B04.rows,CapturedMerkleGlobalArithmetic184L07B05.rows,CapturedMerkleGlobalArithmetic184L07B06.rows,CapturedMerkleGlobalArithmetic184L07B07.rows,CapturedMerkleGlobalArithmetic184L07B08.rows,CapturedMerkleGlobalArithmetic184L07B09.rows,CapturedMerkleGlobalArithmetic184L07B10.rows,CapturedMerkleGlobalArithmetic184L07B11.rows,CapturedMerkleGlobalArithmetic184L07B12.rows,CapturedMerkleGlobalArithmetic184L07B13.rows,CapturedMerkleGlobalArithmetic184L07B14.rows,CapturedMerkleGlobalArithmetic184L07B15.rows,CapturedMerkleGlobalArithmetic184L07B16.rows,CapturedMerkleGlobalArithmetic184L07B17.rows,CapturedMerkleGlobalArithmetic184L07B18.rows,CapturedMerkleGlobalArithmetic184L07B19.rows,CapturedMerkleGlobalArithmetic184L07B20.rows,CapturedMerkleGlobalArithmetic184L07B21.rows,CapturedMerkleGlobalArithmetic184L07B22.rows,CapturedMerkleGlobalArithmetic184L07B23.rows,CapturedMerkleGlobalArithmetic184L07B24.rows,CapturedMerkleGlobalArithmetic184L07B25.rows,CapturedMerkleGlobalArithmetic184L07B26.rows]
 exact ⟨b0,⟨b1,⟨b2,⟨b3,⟨b4,⟨b5,⟨b6,⟨b7,⟨b8,⟨b9,⟨b10,⟨b11,⟨b12,⟨b13,⟨b14,⟨b15,⟨b16,⟨b17,⟨b18,⟨b19,⟨b20,⟨b21,⟨b22,⟨b23,⟨b24,⟨b25,⟨b26,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleFamily32Whole.rows (F:=F) 7) :=
 MerkleArithmeticConstruction253.body_rows base 7 CapturedMerkleGlobalLevel185L07.copy_checked (arithmetic base)
end ShielddSecurity.MerkleCandidateLevel255L07

set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L07.arithmetic
#print axioms ShielddSecurity.MerkleCandidateLevel255L07.arithmetic
set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L07.rows
#print axioms ShielddSecurity.MerkleCandidateLevel255L07.rows
