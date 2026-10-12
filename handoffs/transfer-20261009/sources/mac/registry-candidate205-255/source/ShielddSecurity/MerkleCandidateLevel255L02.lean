import ShielddSecurity.CapturedMerkleGlobalLevel185L02
import ShielddSecurity.MerkleArithmeticConstruction253
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleCandidateLevel255L02
open Compiler CompilerAssertionBlock51 CompilerSelectedChunks172
open CapturedInitial73419Generic01 (p copy)
variable {F : Type} [Field F] [CharP F p]
theorem arithmetic (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleGlobalBody181.arithmeticRows 2) := by
 have b0 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L02B00.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L02B00.indices CapturedMerkleGlobalArithmetic184L02B00.rows CapturedMerkleGlobalArithmetic184L02B00.checked
   change ∀ index∈List.range' 3994 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3994 16 (by omega)
 have b1 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L02B01.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L02B01.indices CapturedMerkleGlobalArithmetic184L02B01.rows CapturedMerkleGlobalArithmetic184L02B01.checked
   change ∀ index∈List.range' 4010 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4010 16 (by omega)
 have b2 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L02B02.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L02B02.indices CapturedMerkleGlobalArithmetic184L02B02.rows CapturedMerkleGlobalArithmetic184L02B02.checked
   change ∀ index∈List.range' 4026 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4026 16 (by omega)
 have b3 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L02B03.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L02B03.indices CapturedMerkleGlobalArithmetic184L02B03.rows CapturedMerkleGlobalArithmetic184L02B03.checked
   change ∀ index∈List.range' 4042 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4042 16 (by omega)
 have b4 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L02B04.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L02B04.indices CapturedMerkleGlobalArithmetic184L02B04.rows CapturedMerkleGlobalArithmetic184L02B04.checked
   change ∀ index∈List.range' 4058 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4058 16 (by omega)
 have b5 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L02B05.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L02B05.indices CapturedMerkleGlobalArithmetic184L02B05.rows CapturedMerkleGlobalArithmetic184L02B05.checked
   change ∀ index∈List.range' 4074 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4074 16 (by omega)
 have b6 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L02B06.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L02B06.indices CapturedMerkleGlobalArithmetic184L02B06.rows CapturedMerkleGlobalArithmetic184L02B06.checked
   change ∀ index∈List.range' 4090 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4090 16 (by omega)
 have b7 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L02B07.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L02B07.indices CapturedMerkleGlobalArithmetic184L02B07.rows CapturedMerkleGlobalArithmetic184L02B07.checked
   change ∀ index∈List.range' 4106 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4106 16 (by omega)
 have b8 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L02B08.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L02B08.indices CapturedMerkleGlobalArithmetic184L02B08.rows CapturedMerkleGlobalArithmetic184L02B08.checked
   change ∀ index∈List.range' 4122 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4122 16 (by omega)
 have b9 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L02B09.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L02B09.indices CapturedMerkleGlobalArithmetic184L02B09.rows CapturedMerkleGlobalArithmetic184L02B09.checked
   change ∀ index∈List.range' 4138 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4138 16 (by omega)
 have b10 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L02B10.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L02B10.indices CapturedMerkleGlobalArithmetic184L02B10.rows CapturedMerkleGlobalArithmetic184L02B10.checked
   change ∀ index∈List.range' 4154 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4154 16 (by omega)
 have b11 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L02B11.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L02B11.indices CapturedMerkleGlobalArithmetic184L02B11.rows CapturedMerkleGlobalArithmetic184L02B11.checked
   change ∀ index∈List.range' 4170 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4170 16 (by omega)
 have b12 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L02B12.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L02B12.indices CapturedMerkleGlobalArithmetic184L02B12.rows CapturedMerkleGlobalArithmetic184L02B12.checked
   change ∀ index∈List.range' 4186 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4186 16 (by omega)
 have b13 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L02B13.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L02B13.indices CapturedMerkleGlobalArithmetic184L02B13.rows CapturedMerkleGlobalArithmetic184L02B13.checked
   change ∀ index∈List.range' 4202 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4202 16 (by omega)
 have b14 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L02B14.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L02B14.indices CapturedMerkleGlobalArithmetic184L02B14.rows CapturedMerkleGlobalArithmetic184L02B14.checked
   change ∀ index∈List.range' 4218 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4218 16 (by omega)
 have b15 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L02B15.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L02B15.indices CapturedMerkleGlobalArithmetic184L02B15.rows CapturedMerkleGlobalArithmetic184L02B15.checked
   change ∀ index∈List.range' 4234 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4234 16 (by omega)
 have b16 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L02B16.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L02B16.indices CapturedMerkleGlobalArithmetic184L02B16.rows CapturedMerkleGlobalArithmetic184L02B16.checked
   change ∀ index∈List.range' 4250 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4250 16 (by omega)
 have b17 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L02B17.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L02B17.indices CapturedMerkleGlobalArithmetic184L02B17.rows CapturedMerkleGlobalArithmetic184L02B17.checked
   change ∀ index∈List.range' 4266 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4266 16 (by omega)
 have b18 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L02B18.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L02B18.indices CapturedMerkleGlobalArithmetic184L02B18.rows CapturedMerkleGlobalArithmetic184L02B18.checked
   change ∀ index∈List.range' 4282 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4282 16 (by omega)
 have b19 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L02B19.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L02B19.indices CapturedMerkleGlobalArithmetic184L02B19.rows CapturedMerkleGlobalArithmetic184L02B19.checked
   change ∀ index∈List.range' 4298 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4298 16 (by omega)
 have b20 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L02B20.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L02B20.indices CapturedMerkleGlobalArithmetic184L02B20.rows CapturedMerkleGlobalArithmetic184L02B20.checked
   change ∀ index∈List.range' 4314 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4314 16 (by omega)
 have b21 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L02B21.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L02B21.indices CapturedMerkleGlobalArithmetic184L02B21.rows CapturedMerkleGlobalArithmetic184L02B21.checked
   change ∀ index∈List.range' 4330 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4330 16 (by omega)
 have b22 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L02B22.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L02B22.indices CapturedMerkleGlobalArithmetic184L02B22.rows CapturedMerkleGlobalArithmetic184L02B22.checked
   change ∀ index∈List.range' 4346 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4346 16 (by omega)
 have b23 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L02B23.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L02B23.indices CapturedMerkleGlobalArithmetic184L02B23.rows CapturedMerkleGlobalArithmetic184L02B23.checked
   change ∀ index∈List.range' 4362 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4362 16 (by omega)
 have b24 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L02B24.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L02B24.indices CapturedMerkleGlobalArithmetic184L02B24.rows CapturedMerkleGlobalArithmetic184L02B24.checked
   change ∀ index∈List.range' 4378 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4378 16 (by omega)
 have b25 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L02B25.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L02B25.indices CapturedMerkleGlobalArithmetic184L02B25.rows CapturedMerkleGlobalArithmetic184L02B25.checked
   change ∀ index∈List.range' 4394 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4394 16 (by omega)
 have b26 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L02B26.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L02B26.indices CapturedMerkleGlobalArithmetic184L02B26.rows CapturedMerkleGlobalArithmetic184L02B26.checked
   change ∀ index∈List.range' 4410 8,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 4410 8 (by omega)
 rw [←CapturedMerkleGlobalLevel185L02.partition]
 apply flatten_sound
 change AllSatisfied (CapturedFullRelation58.candidate base) [CapturedMerkleGlobalArithmetic184L02B00.rows,CapturedMerkleGlobalArithmetic184L02B01.rows,CapturedMerkleGlobalArithmetic184L02B02.rows,CapturedMerkleGlobalArithmetic184L02B03.rows,CapturedMerkleGlobalArithmetic184L02B04.rows,CapturedMerkleGlobalArithmetic184L02B05.rows,CapturedMerkleGlobalArithmetic184L02B06.rows,CapturedMerkleGlobalArithmetic184L02B07.rows,CapturedMerkleGlobalArithmetic184L02B08.rows,CapturedMerkleGlobalArithmetic184L02B09.rows,CapturedMerkleGlobalArithmetic184L02B10.rows,CapturedMerkleGlobalArithmetic184L02B11.rows,CapturedMerkleGlobalArithmetic184L02B12.rows,CapturedMerkleGlobalArithmetic184L02B13.rows,CapturedMerkleGlobalArithmetic184L02B14.rows,CapturedMerkleGlobalArithmetic184L02B15.rows,CapturedMerkleGlobalArithmetic184L02B16.rows,CapturedMerkleGlobalArithmetic184L02B17.rows,CapturedMerkleGlobalArithmetic184L02B18.rows,CapturedMerkleGlobalArithmetic184L02B19.rows,CapturedMerkleGlobalArithmetic184L02B20.rows,CapturedMerkleGlobalArithmetic184L02B21.rows,CapturedMerkleGlobalArithmetic184L02B22.rows,CapturedMerkleGlobalArithmetic184L02B23.rows,CapturedMerkleGlobalArithmetic184L02B24.rows,CapturedMerkleGlobalArithmetic184L02B25.rows,CapturedMerkleGlobalArithmetic184L02B26.rows]
 exact ⟨b0,⟨b1,⟨b2,⟨b3,⟨b4,⟨b5,⟨b6,⟨b7,⟨b8,⟨b9,⟨b10,⟨b11,⟨b12,⟨b13,⟨b14,⟨b15,⟨b16,⟨b17,⟨b18,⟨b19,⟨b20,⟨b21,⟨b22,⟨b23,⟨b24,⟨b25,⟨b26,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleFamily32Whole.rows (F:=F) 2) :=
 MerkleArithmeticConstruction253.body_rows base 2 CapturedMerkleGlobalLevel185L02.copy_checked (arithmetic base)
end ShielddSecurity.MerkleCandidateLevel255L02

set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L02.arithmetic
#print axioms ShielddSecurity.MerkleCandidateLevel255L02.arithmetic
set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L02.rows
#print axioms ShielddSecurity.MerkleCandidateLevel255L02.rows
