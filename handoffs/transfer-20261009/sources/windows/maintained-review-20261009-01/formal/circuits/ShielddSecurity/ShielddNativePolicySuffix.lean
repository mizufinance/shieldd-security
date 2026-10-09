import ShielddSecurity.ShielddNativePolicyDecoder
import ShielddSecurity.ShielddNativePolicyPreparation

set_option maxHeartbeats 250000

namespace ShielddSecurity.ShielddNativePolicySuffix

open GroupByteCodec ShielddNativePolicyDecoder TransferNativeRegulatedSource
  ShielddNativeRegulatedLegality ShielddNativeAddressLegality

structure Cursor where
  raw : List Byte
  position : Nat

/-- These are the globally selected std::str::from_utf8 and upstream
VerificationKey::try_from operations, not a callback returning a wanted policy.
Their native functional instantiation remains an explicit codec boundary. -/
structure Codecs (Key : Type) where
  utf8 : List Byte → Option String
  authority : Bytes → Option Key

structure Route where
  localPort : String
  localChannel : String
  connection : String
  counterpartyPort : String
  counterpartyChannel : String
  deriving DecidableEq

structure Origin where
  route : Route
  baseDenom : String

def routeFields (route : Route) : List String :=
  [route.localPort,route.localChannel,route.connection,route.counterpartyPort,route.counterpartyChannel]

def compareFields : List String → List String → Ordering
  | [],[] => .eq
  | [],_::_ => .lt
  | _::_,[] => .gt
  | left::ls,right::rs => match compare left right with
    | .eq => compareFields ls rs
    | order => order

def insertRoute (value : Route) : List Route → List Route
  | [] => [value]
  | first::rest => match compareFields (routeFields value) (routeFields first) with
    | .gt => first::insertRoute value rest
    | _ => value::first::rest

def sortRoutes : List Route → List Route
  | [] => []
  | first::rest => insertRoute first (sortRoutes rest)

def dedupRoutes : List Route → List Route
  | [] => []
  | first::rest => match rest with
    | [] => [first]
    | next::_ => if first = next then dedupRoutes rest else first::dedupRoutes rest

/-- Independent sort/dedup meaning in IbcRoute's five-field derived Ord order.
Rust's unmodified Vec::sort functional correspondence is separate from this
symbolic expression. This is not canonical_key's NUL-joined view. No route/text
validation or encoding injectivity is asserted by this parser. -/
def canonicalRoutes (routes : List Route) : List Route := dedupRoutes (sortRoutes routes)

def readBytes (count : Nat) (cursor : Cursor) : Option (List Byte × Cursor) :=
  if cursor.position+count ≤ cursor.raw.length then
    some ((cursor.raw.drop cursor.position).take count,⟨cursor.raw,cursor.position+count⟩)
  else none

theorem read_bytes_bounds (count : Nat) (input output : Cursor) (bytes : List Byte)
    (accepted : readBytes count input = some (bytes,output)) :
    output.position = input.position+count ∧ output.raw = input.raw ∧
      output.position ≤ input.raw.length ∧ bytes = (input.raw.drop input.position).take count := by
  by_cases bounded : input.position+count ≤ input.raw.length
  · have same : ((input.raw.drop input.position).take count,
        (⟨input.raw,input.position+count⟩ : Cursor)) = (bytes,output) :=
      Option.some.inj (by simpa only [readBytes,if_pos bounded] using accepted)
    have cursorSame : (⟨input.raw,input.position+count⟩ : Cursor) = output :=
      congrArg Prod.snd same
    rw [← cursorSame]
    exact ⟨rfl,rfl,bounded,(congrArg Prod.fst same).symm⟩
  · simp only [readBytes,if_neg bounded] at accepted
    cases accepted

def readU16 (cursor : Cursor) : Option (Nat × Cursor) := do
  let (bytes,next) ← readBytes 2 cursor
  pure (littleInteger bytes 0 2,next)

def readFlag (cursor : Cursor) : Option (Nat × Cursor) := do
  let (bytes,next) ← readBytes 1 cursor
  pure ((byteAt bytes 0).val,next)

def readString {Key : Type} (codecs : Codecs Key) (cursor : Cursor) : Option (String × Cursor) := do
  let (length,afterLength) ← readU16 cursor
  let (bytes,next) ← readBytes length afterLength
  let text ← codecs.utf8 bytes
  pure (text,next)

def readRoute {Key : Type} (codecs : Codecs Key) (cursor : Cursor) : Option (Route × Cursor) := do
  let (localPort,c1) ← readString codecs cursor
  let (localChannel,c2) ← readString codecs c1
  let (connection,c3) ← readString codecs c2
  let (counterpartyPort,c4) ← readString codecs c3
  let (counterpartyChannel,next) ← readString codecs c4
  pure (⟨localPort,localChannel,connection,counterpartyPort,counterpartyChannel⟩,next)

def readRoutes {Key : Type} (codecs : Codecs Key) : Nat → Cursor → Option (List Route × Cursor)
  | 0,cursor => some ([],cursor)
  | count+1,cursor => do
    let (first,next) ← readRoute codecs cursor
    let (rest,finalCursor) ← readRoutes codecs count next
    pure (first::rest,finalCursor)

def readOrigin {Key : Type} (codecs : Codecs Key) (cursor : Cursor) : Option (Option Origin × Cursor) := do
  let (flag,next) ← readFlag cursor
  if flag = 0 then pure (none,next) else
  if flag = 1 then do
    let (route,afterRoute) ← readRoute codecs next
    let (baseDenom,finalCursor) ← readString codecs afterRoute
    pure (some ⟨route,baseDenom⟩,finalCursor)
  else none

def readAuthority {Key : Type} (codecs : Codecs Key) (cursor : Cursor) : Option (Option Key × Cursor) := do
  let (flag,next) ← readFlag cursor
  if flag = 0 then pure (none,next) else
  if flag = 1 then do
    let (bytes,finalCursor) ← readBytes 32 next
    let key ← codecs.authority (pointBytes bytes 0)
    pure (some key,finalCursor)
  else none

/-- Exact suffix order: route count/routes, origin flag/route/denom, four
strings, registration flag/key, seizure flag/key. Missing/truncated input,
invalid UTF-8, invalid flags or key parsing failure return None. -/
def tailBody {Key : Type} (codecs : Codecs Key) (cursor : Cursor) :
    Option (Tail (List Route) Origin Key × Cursor) := do
  let (count,c1) ← readU16 cursor
  let (routes,c2) ← readRoutes codecs count c1
  let (origin,c3) ← readOrigin codecs c2
  let (ringId,c4) ← readString codecs c3
  let (policyId,c5) ← readString codecs c4
  let (permission,c6) ← readString codecs c5
  let (resource,c7) ← readString codecs c6
  let (registration,c8) ← readAuthority codecs c7
  let (seizure,next) ← readAuthority codecs c8
  pure (⟨canonicalRoutes routes,origin,ringId,policyId,permission,resource,registration,seizure⟩,next)

def parseTail {Key : Type} (codecs : Codecs Key) (raw : List Byte) :
    Option (Tail (List Route) Origin Key) :=
  match tailBody codecs ⟨raw,0⟩ with
  | none => none
  | some (value,cursor) => if cursor.position = raw.length then some value else none

theorem tail_end {Key : Type} (codecs : Codecs Key) (raw : List Byte)
    (value : Tail (List Route) Origin Key) (accepted : parseTail codecs raw = some value) :
    ∃ cursor, tailBody codecs ⟨raw,0⟩ = some (value,cursor) ∧ cursor.position = raw.length := by
  cases parsed : tailBody codecs ⟨raw,0⟩ with
  | none => simp only [parseTail,parsed] at accepted; cases accepted
  | some pair =>
    by_cases finished : pair.2.position = raw.length
    · have same : pair.1 = value :=
        Option.some.inj (by simpa only [parseTail,parsed,if_pos finished] using accepted)
      subst value
      exact ⟨pair.2,rfl,finished⟩
    · simp only [parseTail,parsed,if_neg finished] at accepted
      cases accepted

variable {F : Type} [Field F]
  {E S R K Q Signing J : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {d : F} {model : Group.StandardCurveModel J d}

theorem decoded_points {Key : Type}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (authorityCheck : Key → Bool) (codecs : Codecs Key) (raw : List Byte)
    (policy : Policy S (List Route) Origin (AuditKeys S) Key)
    (accepted : fromBytes upstream authorityCheck (parseTail codecs) raw = some policy) :
    header raw ∧ point upstream (pointBytes raw 4) = some policy.params.issuer ∧
      point upstream (pointBytes raw 52) = some policy.ring.ringKey ∧
      ShielddNativeSdk.nonidentity upstream (pointBytes raw 93) = some policy.ring.auditKeys.payload ∧
      ShielddNativeSdk.nonidentity upstream (pointBytes raw 125) = some policy.ring.auditKeys.checking :=
  decoded_fields upstream authorityCheck (parseTail codecs) raw policy accepted

theorem checked_keys {Key : Type}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (authorityCheck : Key → Bool) (codecs : Codecs Key) (raw : List Byte)
    (policy : Policy S (List Route) Origin (AuditKeys S) Key)
    (hashes : Hashes Q S (List Route) Origin) (leaf : Leaf Q S (AuditKeys S))
    (accepted : fromBytes upstream authorityCheck (parseTail codecs) raw = some policy)
    (matched : checkPolicy hashes leaf policy = some policy) :
    leaf.params.issuer = policy.params.issuer ∧ leaf.ring.ringKey = policy.ring.ringKey ∧
      leaf.ring.auditKeys = policy.ring.auditKeys ∧
      LegalPoint upstream leaf.params.issuer ∧ LegalPoint upstream leaf.ring.ringKey :=
  checked_leaf_keys upstream authorityCheck (parseTail codecs) raw policy hashes leaf accepted matched

theorem prepared_keys {Key : Type}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (authorityCheck : Key → Bool) (codecs : Codecs Key)
    (hashes : Hashes Q S (List Route) Origin) (asset : Q) (assetLeaf : Leaf Q S (AuditKeys S))
    (sender : ShielddNativeActionWitnessAssociation.Sender S Q) (stored : Option (List Byte))
    (source : ShielddNativeActionWitnessAssociation.Source S Q (List Route) Origin Key)
    (prepared : ShielddNativePolicyPreparation.prepare upstream authorityCheck (parseTail codecs)
      asset true assetLeaf sender stored = some source)
    (validated : ShielddNativePolicyPreparation.validatePolicy hashes source = some source) :
    ∃ raw policy, stored = some raw ∧ source.policy = some policy ∧
      fromBytes upstream authorityCheck (parseTail codecs) raw = some policy ∧
      checkPolicy hashes source.assetLeaf policy = some policy ∧
      LegalPoint upstream source.assetLeaf.params.issuer ∧ LegalPoint upstream source.assetLeaf.ring.ringKey :=
  ShielddNativePolicyPreparation.validated_preparation_legal upstream authorityCheck (parseTail codecs)
    hashes asset assetLeaf sender stored source prepared validated

set_option pp.all true in
#check @read_bytes_bounds
#print axioms read_bytes_bounds
set_option pp.all true in
#check @tail_end
#print axioms tail_end
set_option pp.all true in
#check @decoded_points
#print axioms decoded_points
set_option pp.all true in
#check @checked_keys
#print axioms checked_keys
set_option pp.all true in
#check @prepared_keys
#print axioms prepared_keys

end ShielddSecurity.ShielddNativePolicySuffix
