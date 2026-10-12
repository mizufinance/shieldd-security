import ShielddSecurity.CapturedMerkleGlobalLevel185L12
import ShielddSecurity.MerkleArithmeticConstruction253
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleCandidateLevel255L12
open Compiler CompilerAssertionBlock51 CompilerSelectedChunks172
open CapturedInitial73419Generic01 (p copy)
variable {F : Type} [Field F] [CharP F p]
theorem arithmetic (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleGlobalBody181.arithmeticRows 12) := by
 have b0 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L12B00.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L12B00.indices CapturedMerkleGlobalArithmetic184L12B00.rows CapturedMerkleGlobalArithmetic184L12B00.checked
   change ∀ index∈List.range' 8234 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8234 16 (by omega)
 have b1 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L12B01.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L12B01.indices CapturedMerkleGlobalArithmetic184L12B01.rows CapturedMerkleGlobalArithmetic184L12B01.checked
   change ∀ index∈List.range' 8250 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8250 16 (by omega)
 have b2 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L12B02.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L12B02.indices CapturedMerkleGlobalArithmetic184L12B02.rows CapturedMerkleGlobalArithmetic184L12B02.checked
   change ∀ index∈List.range' 8266 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8266 16 (by omega)
 have b3 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L12B03.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L12B03.indices CapturedMerkleGlobalArithmetic184L12B03.rows CapturedMerkleGlobalArithmetic184L12B03.checked
   change ∀ index∈List.range' 8282 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8282 16 (by omega)
 have b4 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L12B04.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L12B04.indices CapturedMerkleGlobalArithmetic184L12B04.rows CapturedMerkleGlobalArithmetic184L12B04.checked
   change ∀ index∈List.range' 8298 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8298 16 (by omega)
 have b5 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L12B05.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L12B05.indices CapturedMerkleGlobalArithmetic184L12B05.rows CapturedMerkleGlobalArithmetic184L12B05.checked
   change ∀ index∈List.range' 8314 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8314 16 (by omega)
 have b6 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L12B06.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L12B06.indices CapturedMerkleGlobalArithmetic184L12B06.rows CapturedMerkleGlobalArithmetic184L12B06.checked
   change ∀ index∈List.range' 8330 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8330 16 (by omega)
 have b7 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L12B07.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L12B07.indices CapturedMerkleGlobalArithmetic184L12B07.rows CapturedMerkleGlobalArithmetic184L12B07.checked
   change ∀ index∈List.range' 8346 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8346 16 (by omega)
 have b8 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L12B08.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L12B08.indices CapturedMerkleGlobalArithmetic184L12B08.rows CapturedMerkleGlobalArithmetic184L12B08.checked
   change ∀ index∈List.range' 8362 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8362 16 (by omega)
 have b9 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L12B09.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L12B09.indices CapturedMerkleGlobalArithmetic184L12B09.rows CapturedMerkleGlobalArithmetic184L12B09.checked
   change ∀ index∈List.range' 8378 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8378 16 (by omega)
 have b10 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L12B10.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L12B10.indices CapturedMerkleGlobalArithmetic184L12B10.rows CapturedMerkleGlobalArithmetic184L12B10.checked
   change ∀ index∈List.range' 8394 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8394 16 (by omega)
 have b11 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L12B11.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L12B11.indices CapturedMerkleGlobalArithmetic184L12B11.rows CapturedMerkleGlobalArithmetic184L12B11.checked
   change ∀ index∈List.range' 8410 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8410 16 (by omega)
 have b12 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L12B12.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L12B12.indices CapturedMerkleGlobalArithmetic184L12B12.rows CapturedMerkleGlobalArithmetic184L12B12.checked
   change ∀ index∈List.range' 8426 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8426 16 (by omega)
 have b13 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L12B13.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L12B13.indices CapturedMerkleGlobalArithmetic184L12B13.rows CapturedMerkleGlobalArithmetic184L12B13.checked
   change ∀ index∈List.range' 8442 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8442 16 (by omega)
 have b14 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L12B14.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L12B14.indices CapturedMerkleGlobalArithmetic184L12B14.rows CapturedMerkleGlobalArithmetic184L12B14.checked
   change ∀ index∈List.range' 8458 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8458 16 (by omega)
 have b15 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L12B15.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L12B15.indices CapturedMerkleGlobalArithmetic184L12B15.rows CapturedMerkleGlobalArithmetic184L12B15.checked
   change ∀ index∈List.range' 8474 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8474 16 (by omega)
 have b16 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L12B16.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L12B16.indices CapturedMerkleGlobalArithmetic184L12B16.rows CapturedMerkleGlobalArithmetic184L12B16.checked
   change ∀ index∈List.range' 8490 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8490 16 (by omega)
 have b17 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L12B17.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L12B17.indices CapturedMerkleGlobalArithmetic184L12B17.rows CapturedMerkleGlobalArithmetic184L12B17.checked
   change ∀ index∈List.range' 8506 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8506 16 (by omega)
 have b18 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L12B18.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L12B18.indices CapturedMerkleGlobalArithmetic184L12B18.rows CapturedMerkleGlobalArithmetic184L12B18.checked
   change ∀ index∈List.range' 8522 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8522 16 (by omega)
 have b19 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L12B19.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L12B19.indices CapturedMerkleGlobalArithmetic184L12B19.rows CapturedMerkleGlobalArithmetic184L12B19.checked
   change ∀ index∈List.range' 8538 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8538 16 (by omega)
 have b20 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L12B20.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L12B20.indices CapturedMerkleGlobalArithmetic184L12B20.rows CapturedMerkleGlobalArithmetic184L12B20.checked
   change ∀ index∈List.range' 8554 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8554 16 (by omega)
 have b21 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L12B21.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L12B21.indices CapturedMerkleGlobalArithmetic184L12B21.rows CapturedMerkleGlobalArithmetic184L12B21.checked
   change ∀ index∈List.range' 8570 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8570 16 (by omega)
 have b22 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L12B22.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L12B22.indices CapturedMerkleGlobalArithmetic184L12B22.rows CapturedMerkleGlobalArithmetic184L12B22.checked
   change ∀ index∈List.range' 8586 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8586 16 (by omega)
 have b23 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L12B23.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L12B23.indices CapturedMerkleGlobalArithmetic184L12B23.rows CapturedMerkleGlobalArithmetic184L12B23.checked
   change ∀ index∈List.range' 8602 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8602 16 (by omega)
 have b24 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L12B24.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L12B24.indices CapturedMerkleGlobalArithmetic184L12B24.rows CapturedMerkleGlobalArithmetic184L12B24.checked
   change ∀ index∈List.range' 8618 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8618 16 (by omega)
 have b25 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L12B25.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L12B25.indices CapturedMerkleGlobalArithmetic184L12B25.rows CapturedMerkleGlobalArithmetic184L12B25.checked
   change ∀ index∈List.range' 8634 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8634 16 (by omega)
 have b26 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L12B26.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L12B26.indices CapturedMerkleGlobalArithmetic184L12B26.rows CapturedMerkleGlobalArithmetic184L12B26.checked
   change ∀ index∈List.range' 8650 8,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 8650 8 (by omega)
 rw [←CapturedMerkleGlobalLevel185L12.partition]
 apply flatten_sound
 change AllSatisfied (CapturedFullRelation58.candidate base) [CapturedMerkleGlobalArithmetic184L12B00.rows,CapturedMerkleGlobalArithmetic184L12B01.rows,CapturedMerkleGlobalArithmetic184L12B02.rows,CapturedMerkleGlobalArithmetic184L12B03.rows,CapturedMerkleGlobalArithmetic184L12B04.rows,CapturedMerkleGlobalArithmetic184L12B05.rows,CapturedMerkleGlobalArithmetic184L12B06.rows,CapturedMerkleGlobalArithmetic184L12B07.rows,CapturedMerkleGlobalArithmetic184L12B08.rows,CapturedMerkleGlobalArithmetic184L12B09.rows,CapturedMerkleGlobalArithmetic184L12B10.rows,CapturedMerkleGlobalArithmetic184L12B11.rows,CapturedMerkleGlobalArithmetic184L12B12.rows,CapturedMerkleGlobalArithmetic184L12B13.rows,CapturedMerkleGlobalArithmetic184L12B14.rows,CapturedMerkleGlobalArithmetic184L12B15.rows,CapturedMerkleGlobalArithmetic184L12B16.rows,CapturedMerkleGlobalArithmetic184L12B17.rows,CapturedMerkleGlobalArithmetic184L12B18.rows,CapturedMerkleGlobalArithmetic184L12B19.rows,CapturedMerkleGlobalArithmetic184L12B20.rows,CapturedMerkleGlobalArithmetic184L12B21.rows,CapturedMerkleGlobalArithmetic184L12B22.rows,CapturedMerkleGlobalArithmetic184L12B23.rows,CapturedMerkleGlobalArithmetic184L12B24.rows,CapturedMerkleGlobalArithmetic184L12B25.rows,CapturedMerkleGlobalArithmetic184L12B26.rows]
 exact ⟨b0,⟨b1,⟨b2,⟨b3,⟨b4,⟨b5,⟨b6,⟨b7,⟨b8,⟨b9,⟨b10,⟨b11,⟨b12,⟨b13,⟨b14,⟨b15,⟨b16,⟨b17,⟨b18,⟨b19,⟨b20,⟨b21,⟨b22,⟨b23,⟨b24,⟨b25,⟨b26,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleFamily32Whole.rows (F:=F) 12) :=
 MerkleArithmeticConstruction253.body_rows base 12 CapturedMerkleGlobalLevel185L12.copy_checked (arithmetic base)
end ShielddSecurity.MerkleCandidateLevel255L12

set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L12.arithmetic
#print axioms ShielddSecurity.MerkleCandidateLevel255L12.arithmetic
set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L12.rows
#print axioms ShielddSecurity.MerkleCandidateLevel255L12.rows
