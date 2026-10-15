import ShielddSecurity.TransferCanonicalWordEquality01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarProgramInvariant01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarWordPrimitives01 (packWords)
open TransferBoundedNativeCodec01 (nullifierModulus)

def certifyResult (words : List UInt64) (width : words.length = 4)
    (canonical : packWords words < nullifierModulus) : CanonicalScalar :=
  { words := ⟨words.toArray, by rw [List.size_toArray]; exact width⟩
    canonical := by
      change packWords words.toArray.toList < nullifierModulus
      rw [List.toList_toArray]
      exact canonical }

set_option pp.all true in
#check @certifyResult
#print axioms certifyResult
end ShielddSecurity.TransferScalarProgramInvariant01
