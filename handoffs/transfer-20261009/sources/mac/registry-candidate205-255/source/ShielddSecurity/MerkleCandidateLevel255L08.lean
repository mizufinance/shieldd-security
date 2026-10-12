import ShielddSecurity.CapturedMerkleGlobalLevel185L08
import ShielddSecurity.MerkleArithmeticConstruction253
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleCandidateLevel255L08
open Compiler CompilerAssertionBlock51 CompilerSelectedChunks172
open CapturedInitial73419Generic01 (p copy)
variable {F : Type} [Field F] [CharP F p]
theorem arithmetic (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleGlobalBody181.arithmeticRows 8) := by
 have b0 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L08B00.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L08B00.indices CapturedMerkleGlobalArithmetic184L08B00.rows CapturedMerkleGlobalArithmetic184L08B00.checked
   change ∀ index∈List.range' 6538 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6538 16 (by omega)
 have b1 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L08B01.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L08B01.indices CapturedMerkleGlobalArithmetic184L08B01.rows CapturedMerkleGlobalArithmetic184L08B01.checked
   change ∀ index∈List.range' 6554 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6554 16 (by omega)
 have b2 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L08B02.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L08B02.indices CapturedMerkleGlobalArithmetic184L08B02.rows CapturedMerkleGlobalArithmetic184L08B02.checked
   change ∀ index∈List.range' 6570 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6570 16 (by omega)
 have b3 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L08B03.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L08B03.indices CapturedMerkleGlobalArithmetic184L08B03.rows CapturedMerkleGlobalArithmetic184L08B03.checked
   change ∀ index∈List.range' 6586 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6586 16 (by omega)
 have b4 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L08B04.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L08B04.indices CapturedMerkleGlobalArithmetic184L08B04.rows CapturedMerkleGlobalArithmetic184L08B04.checked
   change ∀ index∈List.range' 6602 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6602 16 (by omega)
 have b5 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L08B05.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L08B05.indices CapturedMerkleGlobalArithmetic184L08B05.rows CapturedMerkleGlobalArithmetic184L08B05.checked
   change ∀ index∈List.range' 6618 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6618 16 (by omega)
 have b6 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L08B06.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L08B06.indices CapturedMerkleGlobalArithmetic184L08B06.rows CapturedMerkleGlobalArithmetic184L08B06.checked
   change ∀ index∈List.range' 6634 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6634 16 (by omega)
 have b7 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L08B07.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L08B07.indices CapturedMerkleGlobalArithmetic184L08B07.rows CapturedMerkleGlobalArithmetic184L08B07.checked
   change ∀ index∈List.range' 6650 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6650 16 (by omega)
 have b8 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L08B08.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L08B08.indices CapturedMerkleGlobalArithmetic184L08B08.rows CapturedMerkleGlobalArithmetic184L08B08.checked
   change ∀ index∈List.range' 6666 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6666 16 (by omega)
 have b9 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L08B09.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L08B09.indices CapturedMerkleGlobalArithmetic184L08B09.rows CapturedMerkleGlobalArithmetic184L08B09.checked
   change ∀ index∈List.range' 6682 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6682 16 (by omega)
 have b10 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L08B10.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L08B10.indices CapturedMerkleGlobalArithmetic184L08B10.rows CapturedMerkleGlobalArithmetic184L08B10.checked
   change ∀ index∈List.range' 6698 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6698 16 (by omega)
 have b11 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L08B11.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L08B11.indices CapturedMerkleGlobalArithmetic184L08B11.rows CapturedMerkleGlobalArithmetic184L08B11.checked
   change ∀ index∈List.range' 6714 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6714 16 (by omega)
 have b12 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L08B12.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L08B12.indices CapturedMerkleGlobalArithmetic184L08B12.rows CapturedMerkleGlobalArithmetic184L08B12.checked
   change ∀ index∈List.range' 6730 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6730 16 (by omega)
 have b13 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L08B13.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L08B13.indices CapturedMerkleGlobalArithmetic184L08B13.rows CapturedMerkleGlobalArithmetic184L08B13.checked
   change ∀ index∈List.range' 6746 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6746 16 (by omega)
 have b14 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L08B14.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L08B14.indices CapturedMerkleGlobalArithmetic184L08B14.rows CapturedMerkleGlobalArithmetic184L08B14.checked
   change ∀ index∈List.range' 6762 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6762 16 (by omega)
 have b15 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L08B15.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L08B15.indices CapturedMerkleGlobalArithmetic184L08B15.rows CapturedMerkleGlobalArithmetic184L08B15.checked
   change ∀ index∈List.range' 6778 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6778 16 (by omega)
 have b16 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L08B16.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L08B16.indices CapturedMerkleGlobalArithmetic184L08B16.rows CapturedMerkleGlobalArithmetic184L08B16.checked
   change ∀ index∈List.range' 6794 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6794 16 (by omega)
 have b17 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L08B17.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L08B17.indices CapturedMerkleGlobalArithmetic184L08B17.rows CapturedMerkleGlobalArithmetic184L08B17.checked
   change ∀ index∈List.range' 6810 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6810 16 (by omega)
 have b18 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L08B18.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L08B18.indices CapturedMerkleGlobalArithmetic184L08B18.rows CapturedMerkleGlobalArithmetic184L08B18.checked
   change ∀ index∈List.range' 6826 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6826 16 (by omega)
 have b19 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L08B19.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L08B19.indices CapturedMerkleGlobalArithmetic184L08B19.rows CapturedMerkleGlobalArithmetic184L08B19.checked
   change ∀ index∈List.range' 6842 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6842 16 (by omega)
 have b20 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L08B20.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L08B20.indices CapturedMerkleGlobalArithmetic184L08B20.rows CapturedMerkleGlobalArithmetic184L08B20.checked
   change ∀ index∈List.range' 6858 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6858 16 (by omega)
 have b21 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L08B21.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L08B21.indices CapturedMerkleGlobalArithmetic184L08B21.rows CapturedMerkleGlobalArithmetic184L08B21.checked
   change ∀ index∈List.range' 6874 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6874 16 (by omega)
 have b22 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L08B22.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L08B22.indices CapturedMerkleGlobalArithmetic184L08B22.rows CapturedMerkleGlobalArithmetic184L08B22.checked
   change ∀ index∈List.range' 6890 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6890 16 (by omega)
 have b23 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L08B23.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L08B23.indices CapturedMerkleGlobalArithmetic184L08B23.rows CapturedMerkleGlobalArithmetic184L08B23.checked
   change ∀ index∈List.range' 6906 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6906 16 (by omega)
 have b24 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L08B24.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L08B24.indices CapturedMerkleGlobalArithmetic184L08B24.rows CapturedMerkleGlobalArithmetic184L08B24.checked
   change ∀ index∈List.range' 6922 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6922 16 (by omega)
 have b25 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L08B25.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L08B25.indices CapturedMerkleGlobalArithmetic184L08B25.rows CapturedMerkleGlobalArithmetic184L08B25.checked
   change ∀ index∈List.range' 6938 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6938 16 (by omega)
 have b26 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L08B26.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L08B26.indices CapturedMerkleGlobalArithmetic184L08B26.rows CapturedMerkleGlobalArithmetic184L08B26.checked
   change ∀ index∈List.range' 6954 8,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6954 8 (by omega)
 rw [←CapturedMerkleGlobalLevel185L08.partition]
 apply flatten_sound
 change AllSatisfied (CapturedFullRelation58.candidate base) [CapturedMerkleGlobalArithmetic184L08B00.rows,CapturedMerkleGlobalArithmetic184L08B01.rows,CapturedMerkleGlobalArithmetic184L08B02.rows,CapturedMerkleGlobalArithmetic184L08B03.rows,CapturedMerkleGlobalArithmetic184L08B04.rows,CapturedMerkleGlobalArithmetic184L08B05.rows,CapturedMerkleGlobalArithmetic184L08B06.rows,CapturedMerkleGlobalArithmetic184L08B07.rows,CapturedMerkleGlobalArithmetic184L08B08.rows,CapturedMerkleGlobalArithmetic184L08B09.rows,CapturedMerkleGlobalArithmetic184L08B10.rows,CapturedMerkleGlobalArithmetic184L08B11.rows,CapturedMerkleGlobalArithmetic184L08B12.rows,CapturedMerkleGlobalArithmetic184L08B13.rows,CapturedMerkleGlobalArithmetic184L08B14.rows,CapturedMerkleGlobalArithmetic184L08B15.rows,CapturedMerkleGlobalArithmetic184L08B16.rows,CapturedMerkleGlobalArithmetic184L08B17.rows,CapturedMerkleGlobalArithmetic184L08B18.rows,CapturedMerkleGlobalArithmetic184L08B19.rows,CapturedMerkleGlobalArithmetic184L08B20.rows,CapturedMerkleGlobalArithmetic184L08B21.rows,CapturedMerkleGlobalArithmetic184L08B22.rows,CapturedMerkleGlobalArithmetic184L08B23.rows,CapturedMerkleGlobalArithmetic184L08B24.rows,CapturedMerkleGlobalArithmetic184L08B25.rows,CapturedMerkleGlobalArithmetic184L08B26.rows]
 exact ⟨b0,⟨b1,⟨b2,⟨b3,⟨b4,⟨b5,⟨b6,⟨b7,⟨b8,⟨b9,⟨b10,⟨b11,⟨b12,⟨b13,⟨b14,⟨b15,⟨b16,⟨b17,⟨b18,⟨b19,⟨b20,⟨b21,⟨b22,⟨b23,⟨b24,⟨b25,⟨b26,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleFamily32Whole.rows (F:=F) 8) :=
 MerkleArithmeticConstruction253.body_rows base 8 CapturedMerkleGlobalLevel185L08.copy_checked (arithmetic base)
end ShielddSecurity.MerkleCandidateLevel255L08

set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L08.arithmetic
#print axioms ShielddSecurity.MerkleCandidateLevel255L08.arithmetic
set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L08.rows
#print axioms ShielddSecurity.MerkleCandidateLevel255L08.rows
