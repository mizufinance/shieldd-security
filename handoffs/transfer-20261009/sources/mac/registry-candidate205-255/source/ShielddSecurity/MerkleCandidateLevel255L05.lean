import ShielddSecurity.CapturedMerkleGlobalLevel185L05
import ShielddSecurity.MerkleArithmeticConstruction253
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleCandidateLevel255L05
open Compiler CompilerAssertionBlock51 CompilerSelectedChunks172
open CapturedInitial73419Generic01 (p copy)
variable {F : Type} [Field F] [CharP F p]
theorem arithmetic (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleGlobalBody181.arithmeticRows 5) := by
 have b0 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L05B00.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L05B00.indices CapturedMerkleGlobalArithmetic184L05B00.rows CapturedMerkleGlobalArithmetic184L05B00.checked
   change ∀ index∈List.range' 5266 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5266 16 (by omega)
 have b1 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L05B01.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L05B01.indices CapturedMerkleGlobalArithmetic184L05B01.rows CapturedMerkleGlobalArithmetic184L05B01.checked
   change ∀ index∈List.range' 5282 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5282 16 (by omega)
 have b2 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L05B02.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L05B02.indices CapturedMerkleGlobalArithmetic184L05B02.rows CapturedMerkleGlobalArithmetic184L05B02.checked
   change ∀ index∈List.range' 5298 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5298 16 (by omega)
 have b3 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L05B03.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L05B03.indices CapturedMerkleGlobalArithmetic184L05B03.rows CapturedMerkleGlobalArithmetic184L05B03.checked
   change ∀ index∈List.range' 5314 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5314 16 (by omega)
 have b4 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L05B04.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L05B04.indices CapturedMerkleGlobalArithmetic184L05B04.rows CapturedMerkleGlobalArithmetic184L05B04.checked
   change ∀ index∈List.range' 5330 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5330 16 (by omega)
 have b5 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L05B05.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L05B05.indices CapturedMerkleGlobalArithmetic184L05B05.rows CapturedMerkleGlobalArithmetic184L05B05.checked
   change ∀ index∈List.range' 5346 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5346 16 (by omega)
 have b6 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L05B06.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L05B06.indices CapturedMerkleGlobalArithmetic184L05B06.rows CapturedMerkleGlobalArithmetic184L05B06.checked
   change ∀ index∈List.range' 5362 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5362 16 (by omega)
 have b7 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L05B07.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L05B07.indices CapturedMerkleGlobalArithmetic184L05B07.rows CapturedMerkleGlobalArithmetic184L05B07.checked
   change ∀ index∈List.range' 5378 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5378 16 (by omega)
 have b8 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L05B08.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L05B08.indices CapturedMerkleGlobalArithmetic184L05B08.rows CapturedMerkleGlobalArithmetic184L05B08.checked
   change ∀ index∈List.range' 5394 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5394 16 (by omega)
 have b9 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L05B09.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L05B09.indices CapturedMerkleGlobalArithmetic184L05B09.rows CapturedMerkleGlobalArithmetic184L05B09.checked
   change ∀ index∈List.range' 5410 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5410 16 (by omega)
 have b10 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L05B10.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L05B10.indices CapturedMerkleGlobalArithmetic184L05B10.rows CapturedMerkleGlobalArithmetic184L05B10.checked
   change ∀ index∈List.range' 5426 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5426 16 (by omega)
 have b11 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L05B11.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L05B11.indices CapturedMerkleGlobalArithmetic184L05B11.rows CapturedMerkleGlobalArithmetic184L05B11.checked
   change ∀ index∈List.range' 5442 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5442 16 (by omega)
 have b12 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L05B12.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L05B12.indices CapturedMerkleGlobalArithmetic184L05B12.rows CapturedMerkleGlobalArithmetic184L05B12.checked
   change ∀ index∈List.range' 5458 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5458 16 (by omega)
 have b13 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L05B13.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L05B13.indices CapturedMerkleGlobalArithmetic184L05B13.rows CapturedMerkleGlobalArithmetic184L05B13.checked
   change ∀ index∈List.range' 5474 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5474 16 (by omega)
 have b14 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L05B14.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L05B14.indices CapturedMerkleGlobalArithmetic184L05B14.rows CapturedMerkleGlobalArithmetic184L05B14.checked
   change ∀ index∈List.range' 5490 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5490 16 (by omega)
 have b15 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L05B15.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L05B15.indices CapturedMerkleGlobalArithmetic184L05B15.rows CapturedMerkleGlobalArithmetic184L05B15.checked
   change ∀ index∈List.range' 5506 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5506 16 (by omega)
 have b16 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L05B16.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L05B16.indices CapturedMerkleGlobalArithmetic184L05B16.rows CapturedMerkleGlobalArithmetic184L05B16.checked
   change ∀ index∈List.range' 5522 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5522 16 (by omega)
 have b17 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L05B17.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L05B17.indices CapturedMerkleGlobalArithmetic184L05B17.rows CapturedMerkleGlobalArithmetic184L05B17.checked
   change ∀ index∈List.range' 5538 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5538 16 (by omega)
 have b18 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L05B18.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L05B18.indices CapturedMerkleGlobalArithmetic184L05B18.rows CapturedMerkleGlobalArithmetic184L05B18.checked
   change ∀ index∈List.range' 5554 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5554 16 (by omega)
 have b19 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L05B19.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L05B19.indices CapturedMerkleGlobalArithmetic184L05B19.rows CapturedMerkleGlobalArithmetic184L05B19.checked
   change ∀ index∈List.range' 5570 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5570 16 (by omega)
 have b20 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L05B20.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L05B20.indices CapturedMerkleGlobalArithmetic184L05B20.rows CapturedMerkleGlobalArithmetic184L05B20.checked
   change ∀ index∈List.range' 5586 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5586 16 (by omega)
 have b21 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L05B21.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L05B21.indices CapturedMerkleGlobalArithmetic184L05B21.rows CapturedMerkleGlobalArithmetic184L05B21.checked
   change ∀ index∈List.range' 5602 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5602 16 (by omega)
 have b22 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L05B22.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L05B22.indices CapturedMerkleGlobalArithmetic184L05B22.rows CapturedMerkleGlobalArithmetic184L05B22.checked
   change ∀ index∈List.range' 5618 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5618 16 (by omega)
 have b23 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L05B23.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L05B23.indices CapturedMerkleGlobalArithmetic184L05B23.rows CapturedMerkleGlobalArithmetic184L05B23.checked
   change ∀ index∈List.range' 5634 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5634 16 (by omega)
 have b24 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L05B24.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L05B24.indices CapturedMerkleGlobalArithmetic184L05B24.rows CapturedMerkleGlobalArithmetic184L05B24.checked
   change ∀ index∈List.range' 5650 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5650 16 (by omega)
 have b25 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L05B25.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L05B25.indices CapturedMerkleGlobalArithmetic184L05B25.rows CapturedMerkleGlobalArithmetic184L05B25.checked
   change ∀ index∈List.range' 5666 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5666 16 (by omega)
 have b26 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L05B26.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L05B26.indices CapturedMerkleGlobalArithmetic184L05B26.rows CapturedMerkleGlobalArithmetic184L05B26.checked
   change ∀ index∈List.range' 5682 8,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 5682 8 (by omega)
 rw [←CapturedMerkleGlobalLevel185L05.partition]
 apply flatten_sound
 change AllSatisfied (CapturedFullRelation58.candidate base) [CapturedMerkleGlobalArithmetic184L05B00.rows,CapturedMerkleGlobalArithmetic184L05B01.rows,CapturedMerkleGlobalArithmetic184L05B02.rows,CapturedMerkleGlobalArithmetic184L05B03.rows,CapturedMerkleGlobalArithmetic184L05B04.rows,CapturedMerkleGlobalArithmetic184L05B05.rows,CapturedMerkleGlobalArithmetic184L05B06.rows,CapturedMerkleGlobalArithmetic184L05B07.rows,CapturedMerkleGlobalArithmetic184L05B08.rows,CapturedMerkleGlobalArithmetic184L05B09.rows,CapturedMerkleGlobalArithmetic184L05B10.rows,CapturedMerkleGlobalArithmetic184L05B11.rows,CapturedMerkleGlobalArithmetic184L05B12.rows,CapturedMerkleGlobalArithmetic184L05B13.rows,CapturedMerkleGlobalArithmetic184L05B14.rows,CapturedMerkleGlobalArithmetic184L05B15.rows,CapturedMerkleGlobalArithmetic184L05B16.rows,CapturedMerkleGlobalArithmetic184L05B17.rows,CapturedMerkleGlobalArithmetic184L05B18.rows,CapturedMerkleGlobalArithmetic184L05B19.rows,CapturedMerkleGlobalArithmetic184L05B20.rows,CapturedMerkleGlobalArithmetic184L05B21.rows,CapturedMerkleGlobalArithmetic184L05B22.rows,CapturedMerkleGlobalArithmetic184L05B23.rows,CapturedMerkleGlobalArithmetic184L05B24.rows,CapturedMerkleGlobalArithmetic184L05B25.rows,CapturedMerkleGlobalArithmetic184L05B26.rows]
 exact ⟨b0,⟨b1,⟨b2,⟨b3,⟨b4,⟨b5,⟨b6,⟨b7,⟨b8,⟨b9,⟨b10,⟨b11,⟨b12,⟨b13,⟨b14,⟨b15,⟨b16,⟨b17,⟨b18,⟨b19,⟨b20,⟨b21,⟨b22,⟨b23,⟨b24,⟨b25,⟨b26,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleFamily32Whole.rows (F:=F) 5) :=
 MerkleArithmeticConstruction253.body_rows base 5 CapturedMerkleGlobalLevel185L05.copy_checked (arithmetic base)
end ShielddSecurity.MerkleCandidateLevel255L05

set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L05.arithmetic
#print axioms ShielddSecurity.MerkleCandidateLevel255L05.arithmetic
set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L05.rows
#print axioms ShielddSecurity.MerkleCandidateLevel255L05.rows
