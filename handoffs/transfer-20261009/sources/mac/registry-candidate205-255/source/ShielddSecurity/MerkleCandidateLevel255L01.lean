import ShielddSecurity.CapturedMerkleGlobalLevel185L01
import ShielddSecurity.MerkleArithmeticConstruction253
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleCandidateLevel255L01
open Compiler CompilerAssertionBlock51 CompilerSelectedChunks172
open CapturedInitial73419Generic01 (p copy)
variable {F : Type} [Field F] [CharP F p]
theorem arithmetic (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleGlobalBody181.arithmeticRows 1) := by
 have b0 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L01B00.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L01B00.indices CapturedMerkleGlobalArithmetic184L01B00.rows CapturedMerkleGlobalArithmetic184L01B00.checked
   change ∀ index∈List.range' 3570 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3570 16 (by omega)
 have b1 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L01B01.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L01B01.indices CapturedMerkleGlobalArithmetic184L01B01.rows CapturedMerkleGlobalArithmetic184L01B01.checked
   change ∀ index∈List.range' 3586 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3586 16 (by omega)
 have b2 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L01B02.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L01B02.indices CapturedMerkleGlobalArithmetic184L01B02.rows CapturedMerkleGlobalArithmetic184L01B02.checked
   change ∀ index∈List.range' 3602 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3602 16 (by omega)
 have b3 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L01B03.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L01B03.indices CapturedMerkleGlobalArithmetic184L01B03.rows CapturedMerkleGlobalArithmetic184L01B03.checked
   change ∀ index∈List.range' 3618 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3618 16 (by omega)
 have b4 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L01B04.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L01B04.indices CapturedMerkleGlobalArithmetic184L01B04.rows CapturedMerkleGlobalArithmetic184L01B04.checked
   change ∀ index∈List.range' 3634 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3634 16 (by omega)
 have b5 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L01B05.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L01B05.indices CapturedMerkleGlobalArithmetic184L01B05.rows CapturedMerkleGlobalArithmetic184L01B05.checked
   change ∀ index∈List.range' 3650 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3650 16 (by omega)
 have b6 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L01B06.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L01B06.indices CapturedMerkleGlobalArithmetic184L01B06.rows CapturedMerkleGlobalArithmetic184L01B06.checked
   change ∀ index∈List.range' 3666 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3666 16 (by omega)
 have b7 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L01B07.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L01B07.indices CapturedMerkleGlobalArithmetic184L01B07.rows CapturedMerkleGlobalArithmetic184L01B07.checked
   change ∀ index∈List.range' 3682 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3682 16 (by omega)
 have b8 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L01B08.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L01B08.indices CapturedMerkleGlobalArithmetic184L01B08.rows CapturedMerkleGlobalArithmetic184L01B08.checked
   change ∀ index∈List.range' 3698 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3698 16 (by omega)
 have b9 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L01B09.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L01B09.indices CapturedMerkleGlobalArithmetic184L01B09.rows CapturedMerkleGlobalArithmetic184L01B09.checked
   change ∀ index∈List.range' 3714 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3714 16 (by omega)
 have b10 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L01B10.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L01B10.indices CapturedMerkleGlobalArithmetic184L01B10.rows CapturedMerkleGlobalArithmetic184L01B10.checked
   change ∀ index∈List.range' 3730 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3730 16 (by omega)
 have b11 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L01B11.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L01B11.indices CapturedMerkleGlobalArithmetic184L01B11.rows CapturedMerkleGlobalArithmetic184L01B11.checked
   change ∀ index∈List.range' 3746 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3746 16 (by omega)
 have b12 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L01B12.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L01B12.indices CapturedMerkleGlobalArithmetic184L01B12.rows CapturedMerkleGlobalArithmetic184L01B12.checked
   change ∀ index∈List.range' 3762 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3762 16 (by omega)
 have b13 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L01B13.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L01B13.indices CapturedMerkleGlobalArithmetic184L01B13.rows CapturedMerkleGlobalArithmetic184L01B13.checked
   change ∀ index∈List.range' 3778 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3778 16 (by omega)
 have b14 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L01B14.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L01B14.indices CapturedMerkleGlobalArithmetic184L01B14.rows CapturedMerkleGlobalArithmetic184L01B14.checked
   change ∀ index∈List.range' 3794 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3794 16 (by omega)
 have b15 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L01B15.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L01B15.indices CapturedMerkleGlobalArithmetic184L01B15.rows CapturedMerkleGlobalArithmetic184L01B15.checked
   change ∀ index∈List.range' 3810 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3810 16 (by omega)
 have b16 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L01B16.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L01B16.indices CapturedMerkleGlobalArithmetic184L01B16.rows CapturedMerkleGlobalArithmetic184L01B16.checked
   change ∀ index∈List.range' 3826 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3826 16 (by omega)
 have b17 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L01B17.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L01B17.indices CapturedMerkleGlobalArithmetic184L01B17.rows CapturedMerkleGlobalArithmetic184L01B17.checked
   change ∀ index∈List.range' 3842 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3842 16 (by omega)
 have b18 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L01B18.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L01B18.indices CapturedMerkleGlobalArithmetic184L01B18.rows CapturedMerkleGlobalArithmetic184L01B18.checked
   change ∀ index∈List.range' 3858 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3858 16 (by omega)
 have b19 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L01B19.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L01B19.indices CapturedMerkleGlobalArithmetic184L01B19.rows CapturedMerkleGlobalArithmetic184L01B19.checked
   change ∀ index∈List.range' 3874 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3874 16 (by omega)
 have b20 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L01B20.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L01B20.indices CapturedMerkleGlobalArithmetic184L01B20.rows CapturedMerkleGlobalArithmetic184L01B20.checked
   change ∀ index∈List.range' 3890 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3890 16 (by omega)
 have b21 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L01B21.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L01B21.indices CapturedMerkleGlobalArithmetic184L01B21.rows CapturedMerkleGlobalArithmetic184L01B21.checked
   change ∀ index∈List.range' 3906 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3906 16 (by omega)
 have b22 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleWide223Pilot.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleWide223Pilot.indices CapturedMerkleWide223Pilot.rows CapturedMerkleWide223Pilot.checked
   change ∀ index∈List.range' 3922 32,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3922 32 (by omega)
 have b23 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L01B24.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L01B24.indices CapturedMerkleGlobalArithmetic184L01B24.rows CapturedMerkleGlobalArithmetic184L01B24.checked
   change ∀ index∈List.range' 3954 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3954 16 (by omega)
 have b24 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L01B25.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L01B25.indices CapturedMerkleGlobalArithmetic184L01B25.rows CapturedMerkleGlobalArithmetic184L01B25.checked
   change ∀ index∈List.range' 3970 16,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3970 16 (by omega)
 have b25 : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleGlobalArithmetic184L01B26.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleGlobalArithmetic184L01B26.indices CapturedMerkleGlobalArithmetic184L01B26.rows CapturedMerkleGlobalArithmetic184L01B26.checked
   change ∀ index∈List.range' 3986 8,CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported 3986 8 (by omega)
 rw [←CapturedMerkleGlobalLevel185L01.partition]
 apply flatten_sound
 change AllSatisfied (CapturedFullRelation58.candidate base) [CapturedMerkleGlobalArithmetic184L01B00.rows,CapturedMerkleGlobalArithmetic184L01B01.rows,CapturedMerkleGlobalArithmetic184L01B02.rows,CapturedMerkleGlobalArithmetic184L01B03.rows,CapturedMerkleGlobalArithmetic184L01B04.rows,CapturedMerkleGlobalArithmetic184L01B05.rows,CapturedMerkleGlobalArithmetic184L01B06.rows,CapturedMerkleGlobalArithmetic184L01B07.rows,CapturedMerkleGlobalArithmetic184L01B08.rows,CapturedMerkleGlobalArithmetic184L01B09.rows,CapturedMerkleGlobalArithmetic184L01B10.rows,CapturedMerkleGlobalArithmetic184L01B11.rows,CapturedMerkleGlobalArithmetic184L01B12.rows,CapturedMerkleGlobalArithmetic184L01B13.rows,CapturedMerkleGlobalArithmetic184L01B14.rows,CapturedMerkleGlobalArithmetic184L01B15.rows,CapturedMerkleGlobalArithmetic184L01B16.rows,CapturedMerkleGlobalArithmetic184L01B17.rows,CapturedMerkleGlobalArithmetic184L01B18.rows,CapturedMerkleGlobalArithmetic184L01B19.rows,CapturedMerkleGlobalArithmetic184L01B20.rows,CapturedMerkleGlobalArithmetic184L01B21.rows,CapturedMerkleWide223Pilot.rows,CapturedMerkleGlobalArithmetic184L01B24.rows,CapturedMerkleGlobalArithmetic184L01B25.rows,CapturedMerkleGlobalArithmetic184L01B26.rows]
 exact ⟨b0,⟨b1,⟨b2,⟨b3,⟨b4,⟨b5,⟨b6,⟨b7,⟨b8,⟨b9,⟨b10,⟨b11,⟨b12,⟨b13,⟨b14,⟨b15,⟨b16,⟨b17,⟨b18,⟨b19,⟨b20,⟨b21,⟨b22,⟨b23,⟨b24,⟨b25,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleFamily32Whole.rows (F:=F) 1) :=
 MerkleArithmeticConstruction253.body_rows base 1 CapturedMerkleGlobalLevel185L01.copy_checked (arithmetic base)
end ShielddSecurity.MerkleCandidateLevel255L01

set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L01.arithmetic
#print axioms ShielddSecurity.MerkleCandidateLevel255L01.arithmetic
set_option pp.all true in
#check @ShielddSecurity.MerkleCandidateLevel255L01.rows
#print axioms ShielddSecurity.MerkleCandidateLevel255L01.rows
