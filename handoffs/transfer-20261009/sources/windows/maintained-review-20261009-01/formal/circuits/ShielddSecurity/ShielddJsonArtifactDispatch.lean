import ShielddSecurity.ShielddHexSourceSequence

set_option maxHeartbeats 250000

namespace ShielddSecurity.ShielddJsonArtifactDispatch

/- An independent value/visitor recurrence for the exact eight-field Artifact.
JSON syntax, escape decoding, borrow memory and proc-macro/source refinement
are separate. Values below are parsed syntax, never a presumed native Artifact.
Nat count bounds model the actual u64 and the observed 64-bit usize target. -/
inductive Value where
  | string : String → Value
  | number : Nat → Value
  | array : List Value → Value
  | object : List (String × Value) → Value
  | other : Value

def ordered {A B : Type} (decode : A → Option B) : List A → Option (List B)
  | [] => some []
  | first :: rest => do
      let value ← decode first
      let values ← ordered decode rest
      pure (value :: values)

theorem ordered_success {A B : Type} (decode : A → Option B) (encode : B → A)
    (roundtrip : ∀ value, decode (encode value) = some value) (values : List B) :
    ordered decode (values.map encode) = some values := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
    change (decode (encode first)).bind (fun head =>
      (ordered decode (rest.map encode)).bind (fun tail => some (head :: tail))) = _
    rw [roundtrip, ih]
    rfl

def readString : Value → Option String
  | .string value => some value
  | _ => none

def readCount : Value → Option Nat
  | .number value => if value < 2 ^ 64 then some value else none
  | _ => none

def readRow : Value → Option (List String)
  | .array values => ordered readString values
  | _ => none

def readMatrix : Value → Option (List (List String))
  | .array rows => ordered readRow rows
  | _ => none

def matrixValue (rows : List (List String)) : Value :=
  .array (rows.map (fun row => .array (row.map Value.string)))

theorem ordered_matrix (rows : List (List String)) :
    readMatrix (matrixValue rows) = some rows := by
  apply ordered_success readRow (fun row => .array (row.map Value.string)) _ rows
  intro row
  exact ordered_success readString Value.string (fun _ => rfl) row

inductive FieldId where
  | schema | modulus | alpha | fullRounds | partialRounds | skipMatrices | ark | mds
  deriving DecidableEq

def fieldId (name : String) : Option FieldId :=
  if name = "schema" then some .schema else
  if name = "modulus" then some .modulus else
  if name = "alpha" then some .alpha else
  if name = "full_rounds" then some .fullRounds else
  if name = "partial_rounds" then some .partialRounds else
  if name = "skip_matrices" then some .skipMatrices else
  if name = "ark" then some .ark else
  if name = "mds" then some .mds else none

inductive Parsed where
  | string : String → Parsed
  | count : Nat → Parsed
  | matrix : List (List String) → Parsed

def typedField (id : FieldId) (value : Value) : Option Parsed :=
  match id with
  | .schema | .modulus => (readString value).map Parsed.string
  | .alpha | .fullRounds | .partialRounds | .skipMatrices =>
      (readCount value).map Parsed.count
  | .ark | .mds => (readMatrix value).map Parsed.matrix

abbrev Pending := FieldId → Option Parsed

def empty : Pending := fun _ => none

def store (pending : Pending) (id : FieldId) (value : Value) : Option Pending :=
  if (pending id).isSome then none else do
    let parsed ← typedField id value
    pure (fun next => if next = id then some parsed else pending next)

def consume (pending : Pending) (name : String) (value : Value) : Option Pending :=
  match fieldId name with
  | none => some pending
  | some id => store pending id value

def visitMap : List (String × Value) → Pending → Option Pending
  | [], pending => some pending
  | (name, value) :: rest, pending => do
      let next ← consume pending name value
      visitMap rest next

theorem duplicate_field_rejected (pending : Pending) (id : FieldId) (value : Value)
    (present : (pending id).isSome = true) : store pending id value = none := by
  simp [store, present]

theorem unknown_field_ignored (pending : Pending) (name : String) (value : Value)
    (unknown : fieldId name = none) : consume pending name value = some pending := by
  simp only [consume, unknown]

theorem count_type_rejected (text : String) :
    typedField .alpha (.string text) = none := rfl

theorem count_overflow_rejected (value : Nat) (overflow : 2 ^ 64 ≤ value) :
    readCount (.number value) = none := by
  simp only [readCount, if_neg (Nat.not_lt.mpr overflow)]

def parsedString : Option Parsed → Option String
  | some (.string value) => some value
  | _ => none

def parsedCount : Option Parsed → Option Nat
  | some (.count value) => some value
  | _ => none

def parsedMatrix : Option Parsed → Option (List (List String))
  | some (.matrix rows) => some rows
  | _ => none

structure Artifact where
  schema : String
  modulus : String
  alpha : Nat
  fullRounds : Nat
  partialRounds : Nat
  skipMatrices : Nat
  ark : List (List String)
  mds : List (List String)

def materialize (pending : Pending) : Option Artifact := do
  let schema ← parsedString (pending .schema)
  let modulus ← parsedString (pending .modulus)
  let alpha ← parsedCount (pending .alpha)
  let fullRounds ← parsedCount (pending .fullRounds)
  let partialRounds ← parsedCount (pending .partialRounds)
  let skipMatrices ← parsedCount (pending .skipMatrices)
  let ark ← parsedMatrix (pending .ark)
  let mds ← parsedMatrix (pending .mds)
  pure { schema := schema, modulus := modulus, alpha := alpha, fullRounds := fullRounds, partialRounds := partialRounds, skipMatrices := skipMatrices, ark := ark, mds := mds }

def names : List String :=
  ["schema", "modulus", "alpha", "full_rounds", "partial_rounds", "skip_matrices", "ark", "mds"]

def values (artifact : Artifact) : List Value :=
  [.string artifact.schema, .string artifact.modulus, .number artifact.alpha,
   .number artifact.fullRounds, .number artifact.partialRounds, .number artifact.skipMatrices,
   matrixValue artifact.ark, matrixValue artifact.mds]

def objectFields (artifact : Artifact) : List (String × Value) := names.zip (values artifact)

def decodeObject (fields : List (String × Value)) : Option Artifact := do
  let pending ← visitMap fields empty
  materialize pending

def decodeArray (input : List Value) : Option Artifact :=
  if input.length = 8 then decodeObject (names.zip input) else none

def dispatch : Value → Option Artifact
  | .object fields => decodeObject fields
  | .array input => decodeArray input
  | _ => none

theorem missing_schema_rejected (pending : Pending) (missing : pending .schema = none) :
    materialize pending = none := by
  simp [materialize, missing, parsedString]

theorem array_arity_rejected (input : List Value) (wrong : input.length ≠ 8) :
    dispatch (.array input) = none := by
  simp only [dispatch, decodeArray, if_neg wrong]

theorem object_roundtrip (artifact : Artifact)
    (alphaBound : artifact.alpha < 2 ^ 64) (fullBound : artifact.fullRounds < 2 ^ 64)
    (partialBound : artifact.partialRounds < 2 ^ 64) (skipBound : artifact.skipMatrices < 2 ^ 64) :
    dispatch (.object (objectFields artifact)) = some artifact := by
  cases artifact
  simp at alphaBound fullBound partialBound skipBound
  simp [dispatch, objectFields, names, values, decodeObject, visitMap, consume,
    fieldId, store, empty, typedField, readString, readCount, alphaBound, fullBound, partialBound, skipBound,
    ordered_matrix, materialize, parsedString, parsedCount, parsedMatrix]

theorem array_roundtrip (artifact : Artifact)
    (alphaBound : artifact.alpha < 2 ^ 64) (fullBound : artifact.fullRounds < 2 ^ 64)
    (partialBound : artifact.partialRounds < 2 ^ 64) (skipBound : artifact.skipMatrices < 2 ^ 64) :
    dispatch (.array (values artifact)) = some artifact := by
  change (if (values artifact).length = 8 then
    decodeObject (names.zip (values artifact)) else none) = some artifact
  have length : (values artifact).length = 8 := rfl
  rw [if_pos length]
  exact object_roundtrip artifact alphaBound fullBound partialBound skipBound

set_option pp.all true in
#check @ordered_success
#print axioms ordered_success
set_option pp.all true in
#check @ordered_matrix
#print axioms ordered_matrix
set_option pp.all true in
#check @duplicate_field_rejected
#print axioms duplicate_field_rejected
set_option pp.all true in
#check @unknown_field_ignored
#print axioms unknown_field_ignored
set_option pp.all true in
#check @count_type_rejected
#print axioms count_type_rejected
set_option pp.all true in
#check @count_overflow_rejected
#print axioms count_overflow_rejected
set_option pp.all true in
#check @missing_schema_rejected
#print axioms missing_schema_rejected
set_option pp.all true in
#check @array_arity_rejected
#print axioms array_arity_rejected
set_option pp.all true in
#check @object_roundtrip
#print axioms object_roundtrip
set_option pp.all true in
#check @array_roundtrip
#print axioms array_roundtrip

end ShielddSecurity.ShielddJsonArtifactDispatch
