import ShielddSecurity.CapturedMerkleGlobalLevel185L10
import ShielddSecurity.MerkleArithmeticConstruction253
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleCandidateLevel255L10
open Compiler CompilerAssertionBlock51 CompilerSelectedChunks172
open CapturedInitial73419Generic01 (p copy)
variable {F : Type} [Field F] [CharP F p]
theorem arithmetic (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleGlobalBody181.arithmeticRows 10) := by
 have b0 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L10B00.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L10B00.indices CapturedMerkleGlobalArithmetic184L10B00.rows CapturedMerkleGlobalArithmetic184L10B00.checked
   change ∀ index∈List.range' 7386 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7386 16 (by omega)
 have b1 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L10B01.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L10B01.indices CapturedMerkleGlobalArithmetic184L10B01.rows CapturedMerkleGlobalArithmetic184L10B01.checked
   change ∀ index∈List.range' 7402 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7402 16 (by omega)
 have b2 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L10B02.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L10B02.indices CapturedMerkleGlobalArithmetic184L10B02.rows CapturedMerkleGlobalArithmetic184L10B02.checked
   change ∀ index∈List.range' 7418 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7418 16 (by omega)
 have b3 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L10B03.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L10B03.indices CapturedMerkleGlobalArithmetic184L10B03.rows CapturedMerkleGlobalArithmetic184L10B03.checked
   change ∀ index∈List.range' 7434 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7434 16 (by omega)
 have b4 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L10B04.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L10B04.indices CapturedMerkleGlobalArithmetic184L10B04.rows CapturedMerkleGlobalArithmetic184L10B04.checked
   change ∀ index∈List.range' 7450 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7450 16 (by omega)
 have b5 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L10B05.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L10B05.indices CapturedMerkleGlobalArithmetic184L10B05.rows CapturedMerkleGlobalArithmetic184L10B05.checked
   change ∀ index∈List.range' 7466 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7466 16 (by omega)
 have b6 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L10B06.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L10B06.indices CapturedMerkleGlobalArithmetic184L10B06.rows CapturedMerkleGlobalArithmetic184L10B06.checked
   change ∀ index∈List.range' 7482 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7482 16 (by omega)
 have b7 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L10B07.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L10B07.indices CapturedMerkleGlobalArithmetic184L10B07.rows CapturedMerkleGlobalArithmetic184L10B07.checked
   change ∀ index∈List.range' 7498 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7498 16 (by omega)
 have b8 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L10B08.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L10B08.indices CapturedMerkleGlobalArithmetic184L10B08.rows CapturedMerkleGlobalArithmetic184L10B08.checked
   change ∀ index∈List.range' 7514 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7514 16 (by omega)
 have b9 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L10B09.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L10B09.indices CapturedMerkleGlobalArithmetic184L10B09.rows CapturedMerkleGlobalArithmetic184L10B09.checked
   change ∀ index∈List.range' 7530 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7530 16 (by omega)
 have b10 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L10B10.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L10B10.indices CapturedMerkleGlobalArithmetic184L10B10.rows CapturedMerkleGlobalArithmetic184L10B10.checked
   change ∀ index∈List.range' 7546 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7546 16 (by omega)
 have b11 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L10B11.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L10B11.indices CapturedMerkleGlobalArithmetic184L10B11.rows CapturedMerkleGlobalArithmetic184L10B11.checked
   change ∀ index∈List.range' 7562 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7562 16 (by omega)
 have b12 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L10B12.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L10B12.indices CapturedMerkleGlobalArithmetic184L10B12.rows CapturedMerkleGlobalArithmetic184L10B12.checked
   change ∀ index∈List.range' 7578 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7578 16 (by omega)
 have b13 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L10B13.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L10B13.indices CapturedMerkleGlobalArithmetic184L10B13.rows CapturedMerkleGlobalArithmetic184L10B13.checked
   change ∀ index∈List.range' 7594 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7594 16 (by omega)
 have b14 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L10B14.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L10B14.indices CapturedMerkleGlobalArithmetic184L10B14.rows CapturedMerkleGlobalArithmetic184L10B14.checked
   change ∀ index∈List.range' 7610 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7610 16 (by omega)
 have b15 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L10B15.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L10B15.indices CapturedMerkleGlobalArithmetic184L10B15.rows CapturedMerkleGlobalArithmetic184L10B15.checked
   change ∀ index∈List.range' 7626 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7626 16 (by omega)
 have b16 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L10B16.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L10B16.indices CapturedMerkleGlobalArithmetic184L10B16.rows CapturedMerkleGlobalArithmetic184L10B16.checked
   change ∀ index∈List.range' 7642 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7642 16 (by omega)
 have b17 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L10B17.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L10B17.indices CapturedMerkleGlobalArithmetic184L10B17.rows CapturedMerkleGlobalArithmetic184L10B17.checked
   change ∀ index∈List.range' 7658 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7658 16 (by omega)
 have b18 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L10B18.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L10B18.indices CapturedMerkleGlobalArithmetic184L10B18.rows CapturedMerkleGlobalArithmetic184L10B18.checked
   change ∀ index∈List.range' 7674 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7674 16 (by omega)
 have b19 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L10B19.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L10B19.indices CapturedMerkleGlobalArithmetic184L10B19.rows CapturedMerkleGlobalArithmetic184L10B19.checked
   change ∀ index∈List.range' 7690 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7690 16 (by omega)
 have b20 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L10B20.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L10B20.indices CapturedMerkleGlobalArithmetic184L10B20.rows CapturedMerkleGlobalArithmetic184L10B20.checked
   change ∀ index∈List.range' 7706 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7706 16 (by omega)
 have b21 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L10B21.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L10B21.indices CapturedMerkleGlobalArithmetic184L10B21.rows CapturedMerkleGlobalArithmetic184L10B21.checked
   change ∀ index∈List.range' 7722 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7722 16 (by omega)
 have b22 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L10B22.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L10B22.indices CapturedMerkleGlobalArithmetic184L10B22.rows CapturedMerkleGlobalArithmetic184L10B22.checked
   change ∀ index∈List.range' 7738 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7738 16 (by omega)
 have b23 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L10B23.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L10B23.indices CapturedMerkleGlobalArithmetic184L10B23.rows CapturedMerkleGlobalArithmetic184L10B23.checked
   change ∀ index∈List.range' 7754 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7754 16 (by omega)
 have b24 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L10B24.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L10B24.indices CapturedMerkleGlobalArithmetic184L10B24.rows CapturedMerkleGlobalArithmetic184L10B24.checked
   change ∀ index∈List.range' 7770 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7770 16 (by omega)
 have b25 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L10B25.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L10B25.indices CapturedMerkleGlobalArithmetic184L10B25.rows CapturedMerkleGlobalArithmetic184L10B25.checked
   change ∀ index∈List.range' 7786 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7786 16 (by omega)
 have b26 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L10B26.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L10B26.indices CapturedMerkleGlobalArithmetic184L10B26.rows CapturedMerkleGlobalArithmetic184L10B26.checked
   change ∀ index∈List.range' 7802 8,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7802 8 (by omega)
 rw [←CapturedMerkleGlobalLevel185L10.partition]
 apply flatten_sound
 change AllSatisfied (CapturedFullRelation58.candidate base) [CapturedMerkleGlobalArithmetic184L10B00.rows,CapturedMerkleGlobalArithmetic184L10B01.rows,CapturedMerkleGlobalArithmetic184L10B02.rows,CapturedMerkleGlobalArithmetic184L10B03.rows,CapturedMerkleGlobalArithmetic184L10B04.rows,CapturedMerkleGlobalArithmetic184L10B05.rows,CapturedMerkleGlobalArithmetic184L10B06.rows,CapturedMerkleGlobalArithmetic184L10B07.rows,CapturedMerkleGlobalArithmetic184L10B08.rows,CapturedMerkleGlobalArithmetic184L10B09.rows,CapturedMerkleGlobalArithmetic184L10B10.rows,CapturedMerkleGlobalArithmetic184L10B11.rows,CapturedMerkleGlobalArithmetic184L10B12.rows,CapturedMerkleGlobalArithmetic184L10B13.rows,CapturedMerkleGlobalArithmetic184L10B14.rows,CapturedMerkleGlobalArithmetic184L10B15.rows,CapturedMerkleGlobalArithmetic184L10B16.rows,CapturedMerkleGlobalArithmetic184L10B17.rows,CapturedMerkleGlobalArithmetic184L10B18.rows,CapturedMerkleGlobalArithmetic184L10B19.rows,CapturedMerkleGlobalArithmetic184L10B20.rows,CapturedMerkleGlobalArithmetic184L10B21.rows,CapturedMerkleGlobalArithmetic184L10B22.rows,CapturedMerkleGlobalArithmetic184L10B23.rows,CapturedMerkleGlobalArithmetic184L10B24.rows,CapturedMerkleGlobalArithmetic184L10B25.rows,CapturedMerkleGlobalArithmetic184L10B26.rows]
 exact ⟨b0,⟨b1,⟨b2,⟨b3,⟨b4,⟨b5,⟨b6,⟨b7,⟨b8,⟨b9,⟨b10,⟨b11,⟨b12,⟨b13,⟨b14,⟨b15,⟨b16,⟨b17,⟨b18,⟨b19,⟨b20,⟨b21,⟨b22,⟨b23,⟨b24,⟨b25,⟨b26,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleFamily32Whole.rows (F:=F) 10) :=
 MerkleArithmeticConstruction253.body_rows base 10 CapturedMerkleGlobalLevel185L10.copy_checked (arithmetic base)
end ShielddSecurity.MerkleCandidateLevel255L10

set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L10.arithmetic
#print axioms ShielddSecurity.MerkleCandidateLevel255L10.arithmetic
set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L10.rows
#print axioms ShielddSecurity.MerkleCandidateLevel255L10.rows
