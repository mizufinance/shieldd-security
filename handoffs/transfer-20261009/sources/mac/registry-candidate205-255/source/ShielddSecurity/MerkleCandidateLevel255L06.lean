import ShielddSecurity.CapturedMerkleGlobalLevel185L06
import ShielddSecurity.MerkleArithmeticConstruction253
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleCandidateLevel255L06
open Compiler CompilerAssertionBlock51 CompilerSelectedChunks172
open CapturedInitial73419Generic01 (p copy)
variable {F : Type} [Field F] [CharP F p]
theorem arithmetic (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleGlobalBody181.arithmeticRows 6) := by
 have b0 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L06B00.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L06B00.indices CapturedMerkleGlobalArithmetic184L06B00.rows CapturedMerkleGlobalArithmetic184L06B00.checked
   change ∀ index∈List.range' 5690 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5690 16 (by omega)
 have b1 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L06B01.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L06B01.indices CapturedMerkleGlobalArithmetic184L06B01.rows CapturedMerkleGlobalArithmetic184L06B01.checked
   change ∀ index∈List.range' 5706 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5706 16 (by omega)
 have b2 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L06B02.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L06B02.indices CapturedMerkleGlobalArithmetic184L06B02.rows CapturedMerkleGlobalArithmetic184L06B02.checked
   change ∀ index∈List.range' 5722 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5722 16 (by omega)
 have b3 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L06B03.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L06B03.indices CapturedMerkleGlobalArithmetic184L06B03.rows CapturedMerkleGlobalArithmetic184L06B03.checked
   change ∀ index∈List.range' 5738 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5738 16 (by omega)
 have b4 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L06B04.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L06B04.indices CapturedMerkleGlobalArithmetic184L06B04.rows CapturedMerkleGlobalArithmetic184L06B04.checked
   change ∀ index∈List.range' 5754 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5754 16 (by omega)
 have b5 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L06B05.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L06B05.indices CapturedMerkleGlobalArithmetic184L06B05.rows CapturedMerkleGlobalArithmetic184L06B05.checked
   change ∀ index∈List.range' 5770 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5770 16 (by omega)
 have b6 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L06B06.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L06B06.indices CapturedMerkleGlobalArithmetic184L06B06.rows CapturedMerkleGlobalArithmetic184L06B06.checked
   change ∀ index∈List.range' 5786 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5786 16 (by omega)
 have b7 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L06B07.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L06B07.indices CapturedMerkleGlobalArithmetic184L06B07.rows CapturedMerkleGlobalArithmetic184L06B07.checked
   change ∀ index∈List.range' 5802 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5802 16 (by omega)
 have b8 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L06B08.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L06B08.indices CapturedMerkleGlobalArithmetic184L06B08.rows CapturedMerkleGlobalArithmetic184L06B08.checked
   change ∀ index∈List.range' 5818 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5818 16 (by omega)
 have b9 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L06B09.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L06B09.indices CapturedMerkleGlobalArithmetic184L06B09.rows CapturedMerkleGlobalArithmetic184L06B09.checked
   change ∀ index∈List.range' 5834 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5834 16 (by omega)
 have b10 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L06B10.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L06B10.indices CapturedMerkleGlobalArithmetic184L06B10.rows CapturedMerkleGlobalArithmetic184L06B10.checked
   change ∀ index∈List.range' 5850 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5850 16 (by omega)
 have b11 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L06B11.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L06B11.indices CapturedMerkleGlobalArithmetic184L06B11.rows CapturedMerkleGlobalArithmetic184L06B11.checked
   change ∀ index∈List.range' 5866 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5866 16 (by omega)
 have b12 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L06B12.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L06B12.indices CapturedMerkleGlobalArithmetic184L06B12.rows CapturedMerkleGlobalArithmetic184L06B12.checked
   change ∀ index∈List.range' 5882 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5882 16 (by omega)
 have b13 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L06B13.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L06B13.indices CapturedMerkleGlobalArithmetic184L06B13.rows CapturedMerkleGlobalArithmetic184L06B13.checked
   change ∀ index∈List.range' 5898 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5898 16 (by omega)
 have b14 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L06B14.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L06B14.indices CapturedMerkleGlobalArithmetic184L06B14.rows CapturedMerkleGlobalArithmetic184L06B14.checked
   change ∀ index∈List.range' 5914 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5914 16 (by omega)
 have b15 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L06B15.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L06B15.indices CapturedMerkleGlobalArithmetic184L06B15.rows CapturedMerkleGlobalArithmetic184L06B15.checked
   change ∀ index∈List.range' 5930 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5930 16 (by omega)
 have b16 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L06B16.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L06B16.indices CapturedMerkleGlobalArithmetic184L06B16.rows CapturedMerkleGlobalArithmetic184L06B16.checked
   change ∀ index∈List.range' 5946 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5946 16 (by omega)
 have b17 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L06B17.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L06B17.indices CapturedMerkleGlobalArithmetic184L06B17.rows CapturedMerkleGlobalArithmetic184L06B17.checked
   change ∀ index∈List.range' 5962 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5962 16 (by omega)
 have b18 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L06B18.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L06B18.indices CapturedMerkleGlobalArithmetic184L06B18.rows CapturedMerkleGlobalArithmetic184L06B18.checked
   change ∀ index∈List.range' 5978 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5978 16 (by omega)
 have b19 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L06B19.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L06B19.indices CapturedMerkleGlobalArithmetic184L06B19.rows CapturedMerkleGlobalArithmetic184L06B19.checked
   change ∀ index∈List.range' 5994 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5994 16 (by omega)
 have b20 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L06B20.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L06B20.indices CapturedMerkleGlobalArithmetic184L06B20.rows CapturedMerkleGlobalArithmetic184L06B20.checked
   change ∀ index∈List.range' 6010 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6010 16 (by omega)
 have b21 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L06B21.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L06B21.indices CapturedMerkleGlobalArithmetic184L06B21.rows CapturedMerkleGlobalArithmetic184L06B21.checked
   change ∀ index∈List.range' 6026 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6026 16 (by omega)
 have b22 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L06B22.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L06B22.indices CapturedMerkleGlobalArithmetic184L06B22.rows CapturedMerkleGlobalArithmetic184L06B22.checked
   change ∀ index∈List.range' 6042 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6042 16 (by omega)
 have b23 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L06B23.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L06B23.indices CapturedMerkleGlobalArithmetic184L06B23.rows CapturedMerkleGlobalArithmetic184L06B23.checked
   change ∀ index∈List.range' 6058 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6058 16 (by omega)
 have b24 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L06B24.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L06B24.indices CapturedMerkleGlobalArithmetic184L06B24.rows CapturedMerkleGlobalArithmetic184L06B24.checked
   change ∀ index∈List.range' 6074 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6074 16 (by omega)
 have b25 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L06B25.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L06B25.indices CapturedMerkleGlobalArithmetic184L06B25.rows CapturedMerkleGlobalArithmetic184L06B25.checked
   change ∀ index∈List.range' 6090 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6090 16 (by omega)
 have b26 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L06B26.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L06B26.indices CapturedMerkleGlobalArithmetic184L06B26.rows CapturedMerkleGlobalArithmetic184L06B26.checked
   change ∀ index∈List.range' 6106 8,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6106 8 (by omega)
 rw [←CapturedMerkleGlobalLevel185L06.partition]
 apply flatten_sound
 change AllSatisfied (CapturedFullRelation58.candidate base) [CapturedMerkleGlobalArithmetic184L06B00.rows,CapturedMerkleGlobalArithmetic184L06B01.rows,CapturedMerkleGlobalArithmetic184L06B02.rows,CapturedMerkleGlobalArithmetic184L06B03.rows,CapturedMerkleGlobalArithmetic184L06B04.rows,CapturedMerkleGlobalArithmetic184L06B05.rows,CapturedMerkleGlobalArithmetic184L06B06.rows,CapturedMerkleGlobalArithmetic184L06B07.rows,CapturedMerkleGlobalArithmetic184L06B08.rows,CapturedMerkleGlobalArithmetic184L06B09.rows,CapturedMerkleGlobalArithmetic184L06B10.rows,CapturedMerkleGlobalArithmetic184L06B11.rows,CapturedMerkleGlobalArithmetic184L06B12.rows,CapturedMerkleGlobalArithmetic184L06B13.rows,CapturedMerkleGlobalArithmetic184L06B14.rows,CapturedMerkleGlobalArithmetic184L06B15.rows,CapturedMerkleGlobalArithmetic184L06B16.rows,CapturedMerkleGlobalArithmetic184L06B17.rows,CapturedMerkleGlobalArithmetic184L06B18.rows,CapturedMerkleGlobalArithmetic184L06B19.rows,CapturedMerkleGlobalArithmetic184L06B20.rows,CapturedMerkleGlobalArithmetic184L06B21.rows,CapturedMerkleGlobalArithmetic184L06B22.rows,CapturedMerkleGlobalArithmetic184L06B23.rows,CapturedMerkleGlobalArithmetic184L06B24.rows,CapturedMerkleGlobalArithmetic184L06B25.rows,CapturedMerkleGlobalArithmetic184L06B26.rows]
 exact ⟨b0,⟨b1,⟨b2,⟨b3,⟨b4,⟨b5,⟨b6,⟨b7,⟨b8,⟨b9,⟨b10,⟨b11,⟨b12,⟨b13,⟨b14,⟨b15,⟨b16,⟨b17,⟨b18,⟨b19,⟨b20,⟨b21,⟨b22,⟨b23,⟨b24,⟨b25,⟨b26,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleFamily32Whole.rows (F:=F) 6) :=
 MerkleArithmeticConstruction253.body_rows base 6 CapturedMerkleGlobalLevel185L06.copy_checked (arithmetic base)
end ShielddSecurity.MerkleCandidateLevel255L06

set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L06.arithmetic
#print axioms ShielddSecurity.MerkleCandidateLevel255L06.arithmetic
set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L06.rows
#print axioms ShielddSecurity.MerkleCandidateLevel255L06.rows
