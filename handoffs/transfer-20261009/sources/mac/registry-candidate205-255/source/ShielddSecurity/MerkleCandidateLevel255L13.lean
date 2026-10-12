import ShielddSecurity.CapturedMerkleGlobalLevel185L13
import ShielddSecurity.MerkleArithmeticConstruction253
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleCandidateLevel255L13
open Compiler CompilerAssertionBlock51 CompilerSelectedChunks172
open CapturedInitial73419Generic01 (p copy)
variable {F : Type} [Field F] [CharP F p]
theorem arithmetic (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleGlobalBody181.arithmeticRows 13) := by
 have b0 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L13B00.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L13B00.indices CapturedMerkleGlobalArithmetic184L13B00.rows CapturedMerkleGlobalArithmetic184L13B00.checked
   change ∀ index∈List.range' 8658 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8658 16 (by omega)
 have b1 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L13B01.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L13B01.indices CapturedMerkleGlobalArithmetic184L13B01.rows CapturedMerkleGlobalArithmetic184L13B01.checked
   change ∀ index∈List.range' 8674 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8674 16 (by omega)
 have b2 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L13B02.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L13B02.indices CapturedMerkleGlobalArithmetic184L13B02.rows CapturedMerkleGlobalArithmetic184L13B02.checked
   change ∀ index∈List.range' 8690 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8690 16 (by omega)
 have b3 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L13B03.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L13B03.indices CapturedMerkleGlobalArithmetic184L13B03.rows CapturedMerkleGlobalArithmetic184L13B03.checked
   change ∀ index∈List.range' 8706 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8706 16 (by omega)
 have b4 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L13B04.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L13B04.indices CapturedMerkleGlobalArithmetic184L13B04.rows CapturedMerkleGlobalArithmetic184L13B04.checked
   change ∀ index∈List.range' 8722 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8722 16 (by omega)
 have b5 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L13B05.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L13B05.indices CapturedMerkleGlobalArithmetic184L13B05.rows CapturedMerkleGlobalArithmetic184L13B05.checked
   change ∀ index∈List.range' 8738 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8738 16 (by omega)
 have b6 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L13B06.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L13B06.indices CapturedMerkleGlobalArithmetic184L13B06.rows CapturedMerkleGlobalArithmetic184L13B06.checked
   change ∀ index∈List.range' 8754 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8754 16 (by omega)
 have b7 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L13B07.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L13B07.indices CapturedMerkleGlobalArithmetic184L13B07.rows CapturedMerkleGlobalArithmetic184L13B07.checked
   change ∀ index∈List.range' 8770 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8770 16 (by omega)
 have b8 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L13B08.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L13B08.indices CapturedMerkleGlobalArithmetic184L13B08.rows CapturedMerkleGlobalArithmetic184L13B08.checked
   change ∀ index∈List.range' 8786 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8786 16 (by omega)
 have b9 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L13B09.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L13B09.indices CapturedMerkleGlobalArithmetic184L13B09.rows CapturedMerkleGlobalArithmetic184L13B09.checked
   change ∀ index∈List.range' 8802 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8802 16 (by omega)
 have b10 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L13B10.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L13B10.indices CapturedMerkleGlobalArithmetic184L13B10.rows CapturedMerkleGlobalArithmetic184L13B10.checked
   change ∀ index∈List.range' 8818 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8818 16 (by omega)
 have b11 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L13B11.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L13B11.indices CapturedMerkleGlobalArithmetic184L13B11.rows CapturedMerkleGlobalArithmetic184L13B11.checked
   change ∀ index∈List.range' 8834 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8834 16 (by omega)
 have b12 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L13B12.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L13B12.indices CapturedMerkleGlobalArithmetic184L13B12.rows CapturedMerkleGlobalArithmetic184L13B12.checked
   change ∀ index∈List.range' 8850 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8850 16 (by omega)
 have b13 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L13B13.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L13B13.indices CapturedMerkleGlobalArithmetic184L13B13.rows CapturedMerkleGlobalArithmetic184L13B13.checked
   change ∀ index∈List.range' 8866 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8866 16 (by omega)
 have b14 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L13B14.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L13B14.indices CapturedMerkleGlobalArithmetic184L13B14.rows CapturedMerkleGlobalArithmetic184L13B14.checked
   change ∀ index∈List.range' 8882 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8882 16 (by omega)
 have b15 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L13B15.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L13B15.indices CapturedMerkleGlobalArithmetic184L13B15.rows CapturedMerkleGlobalArithmetic184L13B15.checked
   change ∀ index∈List.range' 8898 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8898 16 (by omega)
 have b16 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L13B16.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L13B16.indices CapturedMerkleGlobalArithmetic184L13B16.rows CapturedMerkleGlobalArithmetic184L13B16.checked
   change ∀ index∈List.range' 8914 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8914 16 (by omega)
 have b17 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L13B17.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L13B17.indices CapturedMerkleGlobalArithmetic184L13B17.rows CapturedMerkleGlobalArithmetic184L13B17.checked
   change ∀ index∈List.range' 8930 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8930 16 (by omega)
 have b18 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L13B18.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L13B18.indices CapturedMerkleGlobalArithmetic184L13B18.rows CapturedMerkleGlobalArithmetic184L13B18.checked
   change ∀ index∈List.range' 8946 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8946 16 (by omega)
 have b19 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L13B19.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L13B19.indices CapturedMerkleGlobalArithmetic184L13B19.rows CapturedMerkleGlobalArithmetic184L13B19.checked
   change ∀ index∈List.range' 8962 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8962 16 (by omega)
 have b20 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L13B20.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L13B20.indices CapturedMerkleGlobalArithmetic184L13B20.rows CapturedMerkleGlobalArithmetic184L13B20.checked
   change ∀ index∈List.range' 8978 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8978 16 (by omega)
 have b21 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L13B21.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L13B21.indices CapturedMerkleGlobalArithmetic184L13B21.rows CapturedMerkleGlobalArithmetic184L13B21.checked
   change ∀ index∈List.range' 8994 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8994 16 (by omega)
 have b22 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L13B22.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L13B22.indices CapturedMerkleGlobalArithmetic184L13B22.rows CapturedMerkleGlobalArithmetic184L13B22.checked
   change ∀ index∈List.range' 9010 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9010 16 (by omega)
 have b23 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L13B23.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L13B23.indices CapturedMerkleGlobalArithmetic184L13B23.rows CapturedMerkleGlobalArithmetic184L13B23.checked
   change ∀ index∈List.range' 9026 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9026 16 (by omega)
 have b24 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L13B24.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L13B24.indices CapturedMerkleGlobalArithmetic184L13B24.rows CapturedMerkleGlobalArithmetic184L13B24.checked
   change ∀ index∈List.range' 9042 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9042 16 (by omega)
 have b25 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L13B25.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L13B25.indices CapturedMerkleGlobalArithmetic184L13B25.rows CapturedMerkleGlobalArithmetic184L13B25.checked
   change ∀ index∈List.range' 9058 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9058 16 (by omega)
 have b26 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L13B26.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L13B26.indices CapturedMerkleGlobalArithmetic184L13B26.rows CapturedMerkleGlobalArithmetic184L13B26.checked
   change ∀ index∈List.range' 9074 8,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 9074 8 (by omega)
 rw [←CapturedMerkleGlobalLevel185L13.partition]
 apply flatten_sound
 change AllSatisfied (CapturedFullRelation58.candidate base) [CapturedMerkleGlobalArithmetic184L13B00.rows,CapturedMerkleGlobalArithmetic184L13B01.rows,CapturedMerkleGlobalArithmetic184L13B02.rows,CapturedMerkleGlobalArithmetic184L13B03.rows,CapturedMerkleGlobalArithmetic184L13B04.rows,CapturedMerkleGlobalArithmetic184L13B05.rows,CapturedMerkleGlobalArithmetic184L13B06.rows,CapturedMerkleGlobalArithmetic184L13B07.rows,CapturedMerkleGlobalArithmetic184L13B08.rows,CapturedMerkleGlobalArithmetic184L13B09.rows,CapturedMerkleGlobalArithmetic184L13B10.rows,CapturedMerkleGlobalArithmetic184L13B11.rows,CapturedMerkleGlobalArithmetic184L13B12.rows,CapturedMerkleGlobalArithmetic184L13B13.rows,CapturedMerkleGlobalArithmetic184L13B14.rows,CapturedMerkleGlobalArithmetic184L13B15.rows,CapturedMerkleGlobalArithmetic184L13B16.rows,CapturedMerkleGlobalArithmetic184L13B17.rows,CapturedMerkleGlobalArithmetic184L13B18.rows,CapturedMerkleGlobalArithmetic184L13B19.rows,CapturedMerkleGlobalArithmetic184L13B20.rows,CapturedMerkleGlobalArithmetic184L13B21.rows,CapturedMerkleGlobalArithmetic184L13B22.rows,CapturedMerkleGlobalArithmetic184L13B23.rows,CapturedMerkleGlobalArithmetic184L13B24.rows,CapturedMerkleGlobalArithmetic184L13B25.rows,CapturedMerkleGlobalArithmetic184L13B26.rows]
 exact ⟨b0,⟨b1,⟨b2,⟨b3,⟨b4,⟨b5,⟨b6,⟨b7,⟨b8,⟨b9,⟨b10,⟨b11,⟨b12,⟨b13,⟨b14,⟨b15,⟨b16,⟨b17,⟨b18,⟨b19,⟨b20,⟨b21,⟨b22,⟨b23,⟨b24,⟨b25,⟨b26,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleFamily32Whole.rows (F:=F) 13) :=
 MerkleArithmeticConstruction253.body_rows base 13 CapturedMerkleGlobalLevel185L13.copy_checked (arithmetic base)
end ShielddSecurity.MerkleCandidateLevel255L13

set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L13.arithmetic
#print axioms ShielddSecurity.MerkleCandidateLevel255L13.arithmetic
set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L13.rows
#print axioms ShielddSecurity.MerkleCandidateLevel255L13.rows
