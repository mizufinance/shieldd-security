import ShielddSecurity.TransferScalarReversedByteOrder01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferByteKeyCache01
open TransferStateDelta
open TransferInjectiveKeyPublication01 (keyCode)
/-! Concrete byte-key observation map for the Nat-keyed cache model. The
proved global key encoding injection makes put/delete exact byte updates;
no-write, tombstone, overlay and latest-write merge are preserved. This is
an explicit semantic renaming relation rather than a hash identity argument.
Rust String/UTF8/hash-map/Clone/Any/ownership/trace binding stays separate. -/

def readAtBytes {V : Type} (view : View V) : Bytes → Option V :=
  fun key => view (keyCode key)

def writeAtBytes {V : Type} (writes : Writes V) : Bytes → Option (Option V) :=
  fun key => writes (keyCode key)

def putByteWrite {V : Type} (writes : Bytes → Option (Option V)) (key : Bytes) (value : Option V) :
    Bytes → Option (Option V) :=
  fun other => if other = key then some value else writes other

theorem encoded_key_equality_iff_exact_byte_key_equality (left right : Bytes) :
    keyCode left = keyCode right ↔ left = right :=
  ⟨TransferInjectiveKeyPublication01.keyCode_is_injective, congrArg keyCode⟩

theorem object_put_or_tombstone_is_exact_byte_key_update {O E : Type}
    (delta : Delta O E) (key : Bytes) (value : Option O) :
    writeAtBytes (putObject delta (keyCode key) value).cache.objects =
      putByteWrite (writeAtBytes delta.cache.objects) key value := by
  funext other
  simp only [writeAtBytes, putObject, putByteWrite, encoded_key_equality_iff_exact_byte_key_equality]

theorem byte_key_observation_preserves_overlay_no_write_and_tombstone {V : Type}
    (base : View V) (writes : Writes V) :
    readAtBytes (overlay base writes) =
      (fun key => match writeAtBytes writes key with
        | none => readAtBytes base key
        | some value => value) := rfl

theorem byte_key_observation_preserves_latest_write_merge {V : Type}
    (older newer : Writes V) :
    writeAtBytes (mergeWrites older newer) =
      (fun key => match writeAtBytes newer key with
        | none => writeAtBytes older key
        | some value => some value) := rfl

set_option pp.all true in
#check @readAtBytes
#print axioms readAtBytes
set_option pp.all true in
#check @writeAtBytes
#print axioms writeAtBytes
set_option pp.all true in
#check @putByteWrite
#print axioms putByteWrite
set_option pp.all true in
#check @encoded_key_equality_iff_exact_byte_key_equality
#print axioms encoded_key_equality_iff_exact_byte_key_equality
set_option pp.all true in
#check @object_put_or_tombstone_is_exact_byte_key_update
#print axioms object_put_or_tombstone_is_exact_byte_key_update
set_option pp.all true in
#check @byte_key_observation_preserves_overlay_no_write_and_tombstone
#print axioms byte_key_observation_preserves_overlay_no_write_and_tombstone
set_option pp.all true in
#check @byte_key_observation_preserves_latest_write_merge
#print axioms byte_key_observation_preserves_latest_write_merge
end ShielddSecurity.TransferByteKeyCache01
