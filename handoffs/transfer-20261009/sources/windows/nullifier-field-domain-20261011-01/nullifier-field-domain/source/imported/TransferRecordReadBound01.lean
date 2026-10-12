import ShielddSecurity.TransferDurableWriteSource01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferRecordReadBound01
open TransferStateDelta (Bytes)
/-! Generated from the exact source MAX_RECORD_BYTES expression and source
read_record take/read_to_end/size-check flow. The callback supplies independently
observed returned bytes or read error. Native File/Take/Read semantics, partial
read errors, finite u8/usize/u64 embedding, allocation, ownership and OS state
remain explicit; modeled Nat length matches the source cast on native supported
32/64-bit word domains. No default record, serde validity, whole input consumption,
runtime negative control, native or full Transfer certification is inferred. -/

def recordByteLimit : Nat := 4194304

def sourceTakeLimit : Nat := recordByteLimit + 1

structure Io where
  readToEnd : Nat → Nat → Option Bytes

def readRecord (io : Io) (file : Nat) : Option Bytes :=
  (io.readToEnd file sourceTakeLimit).bind fun bytes =>
    if bytes.length ≤ recordByteLimit then some bytes else none

theorem source_take_limit_is_one_beyond_record_bound_and_fits_supported_words :
    sourceTakeLimit = recordByteLimit + 1 ∧ sourceTakeLimit < 2 ^ 32 ∧ sourceTakeLimit < 2 ^ 64 := by decide

theorem returned_record_derives_actual_bounded_read_bytes (io : Io) (file : Nat) (bytes : Bytes)
    (success : readRecord io file = some bytes) :
    io.readToEnd file sourceTakeLimit = some bytes ∧ bytes.length ≤ recordByteLimit := by
  cases read : io.readToEnd file sourceTakeLimit with
  | none => simp only [readRecord, read, Option.bind_none] at success; contradiction
  | some actual =>
    by_cases bounded : actual.length ≤ recordByteLimit
    · have same : actual = bytes := Option.some.inj (by simpa only [readRecord, read, Option.bind_some, if_pos bounded] using success)
      subst bytes
      exact ⟨rfl, bounded⟩
    · simp only [readRecord, read, Option.bind_some, if_neg bounded] at success
      cases success

theorem oversized_observed_record_refuses (io : Io) (file : Nat) (bytes : Bytes)
    (read : io.readToEnd file sourceTakeLimit = some bytes) (oversized : recordByteLimit < bytes.length) :
    readRecord io file = none := by
  simp only [readRecord, read, Option.bind_some, if_neg (Nat.not_le_of_gt oversized)]

theorem read_error_refuses_without_default (io : Io) (file : Nat)
    (failed : io.readToEnd file sourceTakeLimit = none) : readRecord io file = none := by
  simp only [readRecord, failed, Option.bind_none]

set_option pp.all true in
#check @recordByteLimit
#print axioms recordByteLimit

set_option pp.all true in
#check @sourceTakeLimit
#print axioms sourceTakeLimit

set_option pp.all true in
#check @Io
#print axioms Io

set_option pp.all true in
#check @readRecord
#print axioms readRecord

set_option pp.all true in
#check @source_take_limit_is_one_beyond_record_bound_and_fits_supported_words
#print axioms source_take_limit_is_one_beyond_record_bound_and_fits_supported_words

set_option pp.all true in
#check @returned_record_derives_actual_bounded_read_bytes
#print axioms returned_record_derives_actual_bounded_read_bytes

set_option pp.all true in
#check @oversized_observed_record_refuses
#print axioms oversized_observed_record_refuses

set_option pp.all true in
#check @read_error_refuses_without_default
#print axioms read_error_refuses_without_default
end ShielddSecurity.TransferRecordReadBound01
