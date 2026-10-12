import ShielddSecurity.CapturedMerkleGlobalLevel185L03
import ShielddSecurity.MerkleArithmeticConstruction253
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleCandidateLevel255L03
open Compiler CompilerAssertionBlock51 CompilerSelectedChunks172
open CapturedInitial73419Generic01 (p copy)
variable {F : Type} [Field F] [CharP F p]
theorem arithmetic (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleGlobalBody181.arithmeticRows 3) := by
 have b0 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L03B00.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L03B00.indices CapturedMerkleGlobalArithmetic184L03B00.rows CapturedMerkleGlobalArithmetic184L03B00.checked
   change ∀ index∈List.range' 4418 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4418 16 (by omega)
 have b1 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L03B01.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L03B01.indices CapturedMerkleGlobalArithmetic184L03B01.rows CapturedMerkleGlobalArithmetic184L03B01.checked
   change ∀ index∈List.range' 4434 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4434 16 (by omega)
 have b2 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L03B02.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L03B02.indices CapturedMerkleGlobalArithmetic184L03B02.rows CapturedMerkleGlobalArithmetic184L03B02.checked
   change ∀ index∈List.range' 4450 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4450 16 (by omega)
 have b3 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L03B03.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L03B03.indices CapturedMerkleGlobalArithmetic184L03B03.rows CapturedMerkleGlobalArithmetic184L03B03.checked
   change ∀ index∈List.range' 4466 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4466 16 (by omega)
 have b4 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L03B04.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L03B04.indices CapturedMerkleGlobalArithmetic184L03B04.rows CapturedMerkleGlobalArithmetic184L03B04.checked
   change ∀ index∈List.range' 4482 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4482 16 (by omega)
 have b5 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L03B05.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L03B05.indices CapturedMerkleGlobalArithmetic184L03B05.rows CapturedMerkleGlobalArithmetic184L03B05.checked
   change ∀ index∈List.range' 4498 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4498 16 (by omega)
 have b6 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L03B06.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L03B06.indices CapturedMerkleGlobalArithmetic184L03B06.rows CapturedMerkleGlobalArithmetic184L03B06.checked
   change ∀ index∈List.range' 4514 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4514 16 (by omega)
 have b7 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L03B07.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L03B07.indices CapturedMerkleGlobalArithmetic184L03B07.rows CapturedMerkleGlobalArithmetic184L03B07.checked
   change ∀ index∈List.range' 4530 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4530 16 (by omega)
 have b8 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L03B08.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L03B08.indices CapturedMerkleGlobalArithmetic184L03B08.rows CapturedMerkleGlobalArithmetic184L03B08.checked
   change ∀ index∈List.range' 4546 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4546 16 (by omega)
 have b9 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L03B09.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L03B09.indices CapturedMerkleGlobalArithmetic184L03B09.rows CapturedMerkleGlobalArithmetic184L03B09.checked
   change ∀ index∈List.range' 4562 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4562 16 (by omega)
 have b10 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L03B10.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L03B10.indices CapturedMerkleGlobalArithmetic184L03B10.rows CapturedMerkleGlobalArithmetic184L03B10.checked
   change ∀ index∈List.range' 4578 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4578 16 (by omega)
 have b11 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L03B11.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L03B11.indices CapturedMerkleGlobalArithmetic184L03B11.rows CapturedMerkleGlobalArithmetic184L03B11.checked
   change ∀ index∈List.range' 4594 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4594 16 (by omega)
 have b12 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L03B12.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L03B12.indices CapturedMerkleGlobalArithmetic184L03B12.rows CapturedMerkleGlobalArithmetic184L03B12.checked
   change ∀ index∈List.range' 4610 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4610 16 (by omega)
 have b13 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L03B13.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L03B13.indices CapturedMerkleGlobalArithmetic184L03B13.rows CapturedMerkleGlobalArithmetic184L03B13.checked
   change ∀ index∈List.range' 4626 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4626 16 (by omega)
 have b14 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L03B14.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L03B14.indices CapturedMerkleGlobalArithmetic184L03B14.rows CapturedMerkleGlobalArithmetic184L03B14.checked
   change ∀ index∈List.range' 4642 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4642 16 (by omega)
 have b15 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L03B15.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L03B15.indices CapturedMerkleGlobalArithmetic184L03B15.rows CapturedMerkleGlobalArithmetic184L03B15.checked
   change ∀ index∈List.range' 4658 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4658 16 (by omega)
 have b16 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L03B16.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L03B16.indices CapturedMerkleGlobalArithmetic184L03B16.rows CapturedMerkleGlobalArithmetic184L03B16.checked
   change ∀ index∈List.range' 4674 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4674 16 (by omega)
 have b17 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L03B17.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L03B17.indices CapturedMerkleGlobalArithmetic184L03B17.rows CapturedMerkleGlobalArithmetic184L03B17.checked
   change ∀ index∈List.range' 4690 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4690 16 (by omega)
 have b18 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L03B18.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L03B18.indices CapturedMerkleGlobalArithmetic184L03B18.rows CapturedMerkleGlobalArithmetic184L03B18.checked
   change ∀ index∈List.range' 4706 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4706 16 (by omega)
 have b19 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L03B19.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L03B19.indices CapturedMerkleGlobalArithmetic184L03B19.rows CapturedMerkleGlobalArithmetic184L03B19.checked
   change ∀ index∈List.range' 4722 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4722 16 (by omega)
 have b20 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L03B20.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L03B20.indices CapturedMerkleGlobalArithmetic184L03B20.rows CapturedMerkleGlobalArithmetic184L03B20.checked
   change ∀ index∈List.range' 4738 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4738 16 (by omega)
 have b21 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L03B21.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L03B21.indices CapturedMerkleGlobalArithmetic184L03B21.rows CapturedMerkleGlobalArithmetic184L03B21.checked
   change ∀ index∈List.range' 4754 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4754 16 (by omega)
 have b22 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L03B22.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L03B22.indices CapturedMerkleGlobalArithmetic184L03B22.rows CapturedMerkleGlobalArithmetic184L03B22.checked
   change ∀ index∈List.range' 4770 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4770 16 (by omega)
 have b23 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L03B23.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L03B23.indices CapturedMerkleGlobalArithmetic184L03B23.rows CapturedMerkleGlobalArithmetic184L03B23.checked
   change ∀ index∈List.range' 4786 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4786 16 (by omega)
 have b24 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L03B24.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L03B24.indices CapturedMerkleGlobalArithmetic184L03B24.rows CapturedMerkleGlobalArithmetic184L03B24.checked
   change ∀ index∈List.range' 4802 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4802 16 (by omega)
 have b25 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L03B25.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L03B25.indices CapturedMerkleGlobalArithmetic184L03B25.rows CapturedMerkleGlobalArithmetic184L03B25.checked
   change ∀ index∈List.range' 4818 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4818 16 (by omega)
 have b26 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L03B26.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L03B26.indices CapturedMerkleGlobalArithmetic184L03B26.rows CapturedMerkleGlobalArithmetic184L03B26.checked
   change ∀ index∈List.range' 4834 8,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4834 8 (by omega)
 rw [←CapturedMerkleGlobalLevel185L03.partition]
 apply flatten_sound
 change AllSatisfied (CapturedFullRelation58.candidate base) [CapturedMerkleGlobalArithmetic184L03B00.rows,CapturedMerkleGlobalArithmetic184L03B01.rows,CapturedMerkleGlobalArithmetic184L03B02.rows,CapturedMerkleGlobalArithmetic184L03B03.rows,CapturedMerkleGlobalArithmetic184L03B04.rows,CapturedMerkleGlobalArithmetic184L03B05.rows,CapturedMerkleGlobalArithmetic184L03B06.rows,CapturedMerkleGlobalArithmetic184L03B07.rows,CapturedMerkleGlobalArithmetic184L03B08.rows,CapturedMerkleGlobalArithmetic184L03B09.rows,CapturedMerkleGlobalArithmetic184L03B10.rows,CapturedMerkleGlobalArithmetic184L03B11.rows,CapturedMerkleGlobalArithmetic184L03B12.rows,CapturedMerkleGlobalArithmetic184L03B13.rows,CapturedMerkleGlobalArithmetic184L03B14.rows,CapturedMerkleGlobalArithmetic184L03B15.rows,CapturedMerkleGlobalArithmetic184L03B16.rows,CapturedMerkleGlobalArithmetic184L03B17.rows,CapturedMerkleGlobalArithmetic184L03B18.rows,CapturedMerkleGlobalArithmetic184L03B19.rows,CapturedMerkleGlobalArithmetic184L03B20.rows,CapturedMerkleGlobalArithmetic184L03B21.rows,CapturedMerkleGlobalArithmetic184L03B22.rows,CapturedMerkleGlobalArithmetic184L03B23.rows,CapturedMerkleGlobalArithmetic184L03B24.rows,CapturedMerkleGlobalArithmetic184L03B25.rows,CapturedMerkleGlobalArithmetic184L03B26.rows]
 exact ⟨b0,⟨b1,⟨b2,⟨b3,⟨b4,⟨b5,⟨b6,⟨b7,⟨b8,⟨b9,⟨b10,⟨b11,⟨b12,⟨b13,⟨b14,⟨b15,⟨b16,⟨b17,⟨b18,⟨b19,⟨b20,⟨b21,⟨b22,⟨b23,⟨b24,⟨b25,⟨b26,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleFamily32Whole.rows (F:=F) 3) :=
 MerkleArithmeticConstruction253.body_rows base 3 CapturedMerkleGlobalLevel185L03.copy_checked (arithmetic base)
end ShielddSecurity.MerkleCandidateLevel255L03

set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L03.arithmetic
#print axioms ShielddSecurity.MerkleCandidateLevel255L03.arithmetic
set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L03.rows
#print axioms ShielddSecurity.MerkleCandidateLevel255L03.rows
