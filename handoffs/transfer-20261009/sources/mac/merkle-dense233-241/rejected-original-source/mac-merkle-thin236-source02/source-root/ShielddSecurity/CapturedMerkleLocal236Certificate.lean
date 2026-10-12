import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0018
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleLocal236Certificate
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 268).take 64).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1272)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3890 64
def localParent : Nat → Option Row
 | 3890 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 28),[(26628,1)]⟩
 | 3891 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 29),[(26629,1)]⟩
 | 3892 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 30),[(26631,1)]⟩
 | 3893 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 31),[(26630,4),(26631,1)]⟩
 | 3894 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 32),[(26632,1)]⟩
 | 3895 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 33),[(26633,1)]⟩
 | 3896 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 34),[(26635,1)]⟩
 | 3897 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 35),[(26634,4),(26635,1)]⟩
 | 3898 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 36),[(26636,1)]⟩
 | 3899 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 37),[(26637,1)]⟩
 | 3900 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 38),[(26639,1)]⟩
 | 3901 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 39),[(26638,4),(26639,1)]⟩
 | 3902 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 40),[(26640,1)]⟩
 | 3903 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 41),[(26641,1)]⟩
 | 3904 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 42),[(26643,1)]⟩
 | 3905 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 43),[(26642,4),(26643,1)]⟩
 | 3906 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 44),[(26644,1)]⟩
 | 3907 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 45),[(26645,1)]⟩
 | 3908 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 46),[(26647,1)]⟩
 | 3909 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 47),[(26646,4),(26647,1)]⟩
 | 3910 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 48),[(26648,1)]⟩
 | 3911 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 49),[(26649,1)]⟩
 | 3912 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 50),[(26651,1)]⟩
 | 3913 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 51),[(26650,4),(26651,1)]⟩
 | 3914 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 52),[(26652,1)]⟩
 | 3915 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 53),[(26653,1)]⟩
 | 3916 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 54),[(26655,1)]⟩
 | 3917 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 55),[(26654,4),(26655,1)]⟩
 | 3918 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 56),[(26656,1)]⟩
 | 3919 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 57),[(26657,1)]⟩
 | 3920 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 58),[(26659,1)]⟩
 | 3921 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 59),[(26658,4),(26659,1)]⟩
 | 3922 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 60),[(26660,1)]⟩
 | 3923 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 61),[(26661,1)]⟩
 | 3924 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 62),[(26663,1)]⟩
 | 3925 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 63),[(26662,4),(26663,1)]⟩
 | 3926 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 64),[(26664,1)]⟩
 | 3927 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 65),[(26665,1)]⟩
 | 3928 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 66),[(26667,1)]⟩
 | 3929 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 67),[(26666,4),(26667,1)]⟩
 | 3930 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 68),[(26668,1)]⟩
 | 3931 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 69),[(26669,1)]⟩
 | 3932 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 70),[(26671,1)]⟩
 | 3933 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 71),[(26670,4),(26671,1)]⟩
 | 3934 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 72),[(26672,1)]⟩
 | 3935 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 73),[(26673,1)]⟩
 | 3936 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 74),[(26675,1)]⟩
 | 3937 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 75),[(26674,4),(26675,1)]⟩
 | 3938 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 76),[(26676,1)]⟩
 | 3939 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 77),[(26677,1)]⟩
 | 3940 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 78),[(26679,1)]⟩
 | 3941 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 79),[(26678,4),(26679,1)]⟩
 | 3942 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 80),[(26680,1)]⟩
 | 3943 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 81),[(26681,1)]⟩
 | 3944 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 82),[(26683,1)]⟩
 | 3945 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 83),[(26682,4),(26683,1)]⟩
 | 3946 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 84),[(26684,1)]⟩
 | 3947 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 85),[(26685,1)]⟩
 | 3948 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 86),[(26687,1)]⟩
 | 3949 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 87),[(26686,4),(26687,1)]⟩
 | 3950 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 88),[(26688,1)]⟩
 | 3951 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 89),[(26689,1)]⟩
 | 3952 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 90),[(26691,1)]⟩
 | 3953 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 91),[(26690,4),(26691,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=64 := by rfl
end ShielddSecurity.CapturedMerkleLocal236Certificate

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleLocal236Certificate.rows
#print axioms ShielddSecurity.CapturedMerkleLocal236Certificate.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleLocal236Certificate.indices
#print axioms ShielddSecurity.CapturedMerkleLocal236Certificate.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleLocal236Certificate.localParent
#print axioms ShielddSecurity.CapturedMerkleLocal236Certificate.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleLocal236Certificate.localCheck
#print axioms ShielddSecurity.CapturedMerkleLocal236Certificate.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleLocal236Certificate.local_checked
#print axioms ShielddSecurity.CapturedMerkleLocal236Certificate.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleLocal236Certificate.count
#print axioms ShielddSecurity.CapturedMerkleLocal236Certificate.count
