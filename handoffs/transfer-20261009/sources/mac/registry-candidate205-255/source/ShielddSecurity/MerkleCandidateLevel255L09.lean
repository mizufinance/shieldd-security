import ShielddSecurity.CapturedMerkleGlobalLevel185L09
import ShielddSecurity.MerkleArithmeticConstruction253
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleCandidateLevel255L09
open Compiler CompilerAssertionBlock51 CompilerSelectedChunks172
open CapturedInitial73419Generic01 (p copy)
variable {F : Type} [Field F] [CharP F p]
theorem arithmetic (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleGlobalBody181.arithmeticRows 9) := by
 have b0 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L09B00.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L09B00.indices CapturedMerkleGlobalArithmetic184L09B00.rows CapturedMerkleGlobalArithmetic184L09B00.checked
   change ∀ index∈List.range' 6962 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6962 16 (by omega)
 have b1 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L09B01.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L09B01.indices CapturedMerkleGlobalArithmetic184L09B01.rows CapturedMerkleGlobalArithmetic184L09B01.checked
   change ∀ index∈List.range' 6978 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6978 16 (by omega)
 have b2 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L09B02.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L09B02.indices CapturedMerkleGlobalArithmetic184L09B02.rows CapturedMerkleGlobalArithmetic184L09B02.checked
   change ∀ index∈List.range' 6994 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 6994 16 (by omega)
 have b3 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L09B03.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L09B03.indices CapturedMerkleGlobalArithmetic184L09B03.rows CapturedMerkleGlobalArithmetic184L09B03.checked
   change ∀ index∈List.range' 7010 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7010 16 (by omega)
 have b4 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L09B04.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L09B04.indices CapturedMerkleGlobalArithmetic184L09B04.rows CapturedMerkleGlobalArithmetic184L09B04.checked
   change ∀ index∈List.range' 7026 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7026 16 (by omega)
 have b5 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L09B05.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L09B05.indices CapturedMerkleGlobalArithmetic184L09B05.rows CapturedMerkleGlobalArithmetic184L09B05.checked
   change ∀ index∈List.range' 7042 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7042 16 (by omega)
 have b6 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L09B06.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L09B06.indices CapturedMerkleGlobalArithmetic184L09B06.rows CapturedMerkleGlobalArithmetic184L09B06.checked
   change ∀ index∈List.range' 7058 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7058 16 (by omega)
 have b7 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L09B07.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L09B07.indices CapturedMerkleGlobalArithmetic184L09B07.rows CapturedMerkleGlobalArithmetic184L09B07.checked
   change ∀ index∈List.range' 7074 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7074 16 (by omega)
 have b8 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L09B08.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L09B08.indices CapturedMerkleGlobalArithmetic184L09B08.rows CapturedMerkleGlobalArithmetic184L09B08.checked
   change ∀ index∈List.range' 7090 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7090 16 (by omega)
 have b9 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L09B09.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L09B09.indices CapturedMerkleGlobalArithmetic184L09B09.rows CapturedMerkleGlobalArithmetic184L09B09.checked
   change ∀ index∈List.range' 7106 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7106 16 (by omega)
 have b10 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L09B10.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L09B10.indices CapturedMerkleGlobalArithmetic184L09B10.rows CapturedMerkleGlobalArithmetic184L09B10.checked
   change ∀ index∈List.range' 7122 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7122 16 (by omega)
 have b11 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L09B11.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L09B11.indices CapturedMerkleGlobalArithmetic184L09B11.rows CapturedMerkleGlobalArithmetic184L09B11.checked
   change ∀ index∈List.range' 7138 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7138 16 (by omega)
 have b12 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L09B12.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L09B12.indices CapturedMerkleGlobalArithmetic184L09B12.rows CapturedMerkleGlobalArithmetic184L09B12.checked
   change ∀ index∈List.range' 7154 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7154 16 (by omega)
 have b13 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L09B13.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L09B13.indices CapturedMerkleGlobalArithmetic184L09B13.rows CapturedMerkleGlobalArithmetic184L09B13.checked
   change ∀ index∈List.range' 7170 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7170 16 (by omega)
 have b14 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L09B14.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L09B14.indices CapturedMerkleGlobalArithmetic184L09B14.rows CapturedMerkleGlobalArithmetic184L09B14.checked
   change ∀ index∈List.range' 7186 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7186 16 (by omega)
 have b15 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L09B15.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L09B15.indices CapturedMerkleGlobalArithmetic184L09B15.rows CapturedMerkleGlobalArithmetic184L09B15.checked
   change ∀ index∈List.range' 7202 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7202 16 (by omega)
 have b16 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L09B16.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L09B16.indices CapturedMerkleGlobalArithmetic184L09B16.rows CapturedMerkleGlobalArithmetic184L09B16.checked
   change ∀ index∈List.range' 7218 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7218 16 (by omega)
 have b17 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L09B17.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L09B17.indices CapturedMerkleGlobalArithmetic184L09B17.rows CapturedMerkleGlobalArithmetic184L09B17.checked
   change ∀ index∈List.range' 7234 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7234 16 (by omega)
 have b18 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L09B18.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L09B18.indices CapturedMerkleGlobalArithmetic184L09B18.rows CapturedMerkleGlobalArithmetic184L09B18.checked
   change ∀ index∈List.range' 7250 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7250 16 (by omega)
 have b19 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L09B19.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L09B19.indices CapturedMerkleGlobalArithmetic184L09B19.rows CapturedMerkleGlobalArithmetic184L09B19.checked
   change ∀ index∈List.range' 7266 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7266 16 (by omega)
 have b20 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L09B20.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L09B20.indices CapturedMerkleGlobalArithmetic184L09B20.rows CapturedMerkleGlobalArithmetic184L09B20.checked
   change ∀ index∈List.range' 7282 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7282 16 (by omega)
 have b21 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L09B21.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L09B21.indices CapturedMerkleGlobalArithmetic184L09B21.rows CapturedMerkleGlobalArithmetic184L09B21.checked
   change ∀ index∈List.range' 7298 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7298 16 (by omega)
 have b22 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L09B22.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L09B22.indices CapturedMerkleGlobalArithmetic184L09B22.rows CapturedMerkleGlobalArithmetic184L09B22.checked
   change ∀ index∈List.range' 7314 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7314 16 (by omega)
 have b23 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L09B23.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L09B23.indices CapturedMerkleGlobalArithmetic184L09B23.rows CapturedMerkleGlobalArithmetic184L09B23.checked
   change ∀ index∈List.range' 7330 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7330 16 (by omega)
 have b24 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L09B24.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L09B24.indices CapturedMerkleGlobalArithmetic184L09B24.rows CapturedMerkleGlobalArithmetic184L09B24.checked
   change ∀ index∈List.range' 7346 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7346 16 (by omega)
 have b25 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L09B25.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L09B25.indices CapturedMerkleGlobalArithmetic184L09B25.rows CapturedMerkleGlobalArithmetic184L09B25.checked
   change ∀ index∈List.range' 7362 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7362 16 (by omega)
 have b26 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L09B26.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L09B26.indices CapturedMerkleGlobalArithmetic184L09B26.rows CapturedMerkleGlobalArithmetic184L09B26.checked
   change ∀ index∈List.range' 7378 8,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 7378 8 (by omega)
 rw [←CapturedMerkleGlobalLevel185L09.partition]
 apply flatten_sound
 change AllSatisfied (CapturedFullRelation58.candidate base) [CapturedMerkleGlobalArithmetic184L09B00.rows,CapturedMerkleGlobalArithmetic184L09B01.rows,CapturedMerkleGlobalArithmetic184L09B02.rows,CapturedMerkleGlobalArithmetic184L09B03.rows,CapturedMerkleGlobalArithmetic184L09B04.rows,CapturedMerkleGlobalArithmetic184L09B05.rows,CapturedMerkleGlobalArithmetic184L09B06.rows,CapturedMerkleGlobalArithmetic184L09B07.rows,CapturedMerkleGlobalArithmetic184L09B08.rows,CapturedMerkleGlobalArithmetic184L09B09.rows,CapturedMerkleGlobalArithmetic184L09B10.rows,CapturedMerkleGlobalArithmetic184L09B11.rows,CapturedMerkleGlobalArithmetic184L09B12.rows,CapturedMerkleGlobalArithmetic184L09B13.rows,CapturedMerkleGlobalArithmetic184L09B14.rows,CapturedMerkleGlobalArithmetic184L09B15.rows,CapturedMerkleGlobalArithmetic184L09B16.rows,CapturedMerkleGlobalArithmetic184L09B17.rows,CapturedMerkleGlobalArithmetic184L09B18.rows,CapturedMerkleGlobalArithmetic184L09B19.rows,CapturedMerkleGlobalArithmetic184L09B20.rows,CapturedMerkleGlobalArithmetic184L09B21.rows,CapturedMerkleGlobalArithmetic184L09B22.rows,CapturedMerkleGlobalArithmetic184L09B23.rows,CapturedMerkleGlobalArithmetic184L09B24.rows,CapturedMerkleGlobalArithmetic184L09B25.rows,CapturedMerkleGlobalArithmetic184L09B26.rows]
 exact ⟨b0,⟨b1,⟨b2,⟨b3,⟨b4,⟨b5,⟨b6,⟨b7,⟨b8,⟨b9,⟨b10,⟨b11,⟨b12,⟨b13,⟨b14,⟨b15,⟨b16,⟨b17,⟨b18,⟨b19,⟨b20,⟨b21,⟨b22,⟨b23,⟨b24,⟨b25,⟨b26,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleFamily32Whole.rows (F:=F) 9) :=
 MerkleArithmeticConstruction253.body_rows base 9 CapturedMerkleGlobalLevel185L09.copy_checked (arithmetic base)
end ShielddSecurity.MerkleCandidateLevel255L09

set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L09.arithmetic
#print axioms ShielddSecurity.MerkleCandidateLevel255L09.arithmetic
set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L09.rows
#print axioms ShielddSecurity.MerkleCandidateLevel255L09.rows
