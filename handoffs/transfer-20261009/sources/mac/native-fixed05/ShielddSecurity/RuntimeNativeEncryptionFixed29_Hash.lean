import ShielddSecurity.RuntimeNativeEncryptionFixed29_Rounds_00_04
import ShielddSecurity.RuntimeNativeEncryptionFixed29_Rounds_05_09
import ShielddSecurity.RuntimeNativeEncryptionFixed29_Rounds_10_14
import ShielddSecurity.RuntimeNativeEncryptionFixed29_Rounds_15_19
import ShielddSecurity.RuntimeNativeEncryptionFixed29_Rounds_20_24
import ShielddSecurity.RuntimeNativeEncryptionFixed29_Rounds_25_29
import ShielddSecurity.RuntimeNativeEncryptionFixed29_Rounds_30_34
import ShielddSecurity.RuntimeNativeEncryptionFixed29_Rounds_35_39
import ShielddSecurity.RuntimeNativeEncryptionFixed29_Rounds_40_44
import ShielddSecurity.RuntimeNativeEncryptionFixed29_Rounds_45_49
import ShielddSecurity.RuntimeNativeEncryptionFixed29_Rounds_50_54
import ShielddSecurity.RuntimeNativeEncryptionFixed29_Rounds_55_59
import ShielddSecurity.RuntimeNativeEncryptionFixed29_Rounds_60_64
set_option maxHeartbeats 250000
set_option maxRecDepth 2048
namespace ShielddSecurity.RuntimeNativeEncryptionFixed29
theorem steps (index : Nat) (bounded : index < 65) : states (index + 1) =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters index (states index) := by
  interval_cases index <;> first
    | exact step00
    | exact step01
    | exact step02
    | exact step03
    | exact step04
    | exact step05
    | exact step06
    | exact step07
    | exact step08
    | exact step09
    | exact step10
    | exact step11
    | exact step12
    | exact step13
    | exact step14
    | exact step15
    | exact step16
    | exact step17
    | exact step18
    | exact step19
    | exact step20
    | exact step21
    | exact step22
    | exact step23
    | exact step24
    | exact step25
    | exact step26
    | exact step27
    | exact step28
    | exact step29
    | exact step30
    | exact step31
    | exact step32
    | exact step33
    | exact step34
    | exact step35
    | exact step36
    | exact step37
    | exact step38
    | exact step39
    | exact step40
    | exact step41
    | exact step42
    | exact step43
    | exact step44
    | exact step45
    | exact step46
    | exact step47
    | exact step48
    | exact step49
    | exact step50
    | exact step51
    | exact step52
    | exact step53
    | exact step54
    | exact step55
    | exact step56
    | exact step57
    | exact step58
    | exact step59
    | exact step60
    | exact step61
    | exact step62
    | exact step63
    | exact step64
theorem hash_value {F : Type} [Field F] [CharP F Scalar.modulus] :
    Poseidon.hash3 NativeAssetHashParameters.smallParameters 29 [] =
      (47127370616510101739034211210395480563266834468464461032177054264535895577291 : F) := by
  simpa only [states, Int.cast_ofNat] using
    (NativeEncryptionFixedArithmetic.fixed_empty_hash_trace (F := F) 29 states initial steps)
set_option pp.all true in
#check @steps
#print axioms steps
set_option pp.all true in
#check @hash_value
#print axioms hash_value
end ShielddSecurity.RuntimeNativeEncryptionFixed29
