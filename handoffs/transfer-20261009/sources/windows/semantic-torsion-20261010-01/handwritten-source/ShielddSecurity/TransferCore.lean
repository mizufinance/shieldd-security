import Mathlib.Data.Int.Basic
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 4096
set_option maxHeartbeats 200000

/-! Independent integer/branch Transfer intent. These definitions contain no rows,
compiler handles, Rust witness callbacks, history selectors or desired-fact record.
Cryptographic equations and production refinement are deliberately outstanding. -/
namespace ShielddSecurity.TransferCore

def amountBound : Nat := 2 ^ 128
def fieldModulus : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513
def scalarOrder : Nat :=
  6554484396890773809930967563523245729705921265872317281365359162392183254199

structure Affine where
  x : Nat
  y : Nat
  deriving DecidableEq

structure Address where
  diversified : Affine
  transmission : Affine
  deriving DecidableEq

def CanonicalAffine (point : Affine) : Prop :=
  point.x < fieldModulus ∧ point.y < fieldModulus

structure Note where
  owner : Address
  asset : Nat
  amount : Nat
  blinding : Nat
  recovery : Nat

structure RealSpend where
  note : Note
  /-- Quaternary depth 24: a position has 48 bits, not 24. -/
  position : Nat
  siblings : Fin 24 → Fin 3 → Nat
  nullifier : Nat

structure DummySpend where
  amount : Nat
  seed : Nat
  nullifier : Nat

inductive OptionalSpend
  | real (spend : RealSpend)
  | dummy (spend : DummySpend)

def OptionalSpend.amount : OptionalSpend → Nat
  | .real spend => spend.note.amount
  | .dummy spend => spend.amount

structure Witness where
  sender : Address
  receiver : Address
  asset : Nat
  required : RealSpend
  optional : OptionalSpend
  receiverOutput : Note
  changeOutput : Note
  balanceBlinding : Nat

def RealInputIntent (owner : Address) (asset : Nat) (input : RealSpend) : Prop :=
  input.note.owner = owner ∧ input.note.asset = asset ∧
  input.note.amount < amountBound ∧ input.position < 2 ^ 48

def OptionalInputIntent (owner : Address) (asset : Nat) : OptionalSpend → Prop
  | .real spend => RealInputIntent owner asset spend
  | .dummy spend => spend.amount = 0

def CoreIntent (w : Witness) : Prop :=
  RealInputIntent w.sender w.asset w.required ∧
  OptionalInputIntent w.sender w.asset w.optional ∧
  w.receiverOutput.owner = w.receiver ∧ w.changeOutput.owner = w.sender ∧
  w.receiverOutput.asset = w.asset ∧ w.changeOutput.asset = w.asset ∧
  0 < w.receiverOutput.amount ∧ w.receiverOutput.amount < amountBound ∧
  w.changeOutput.amount < amountBound ∧ w.balanceBlinding < scalarOrder

/-- The action contributes its signed net. Zero net is not a legality premise. -/
def netAmount (w : Witness) : Int :=
  (w.required.note.amount : Int) + (w.optional.amount : Int) -
  (w.receiverOutput.amount : Int) - (w.changeOutput.amount : Int)

/-- Circuit field negation and scalar group negation have different moduli. -/
def signedResidue (modulus : Nat) (amount : Int) : Int := amount % (modulus : Int)

theorem optional_amount_bounded (owner : Address) (asset : Nat) (spend : OptionalSpend)
    (legal : OptionalInputIntent owner asset spend) : spend.amount < amountBound := by
  cases spend with
  | real input => exact legal.2.2.1
  | dummy input => simp only [OptionalInputIntent] at legal; simp [OptionalSpend.amount, legal, amountBound]

/-- Independent legal inputs prevent integer net overflow; no circuit soundness
is asserted. Bounds must later be reconstructed from arbitrary actual rows. -/
theorem net_amount_bounded (w : Witness) (legal : CoreIntent w) :
    -(2 * (amountBound : Int)) < netAmount w ∧
    netAmount w < 2 * (amountBound : Int) := by
  have required := legal.1.2.2.1
  have optional := optional_amount_bounded w.sender w.asset w.optional legal.2.1
  have receiver := legal.2.2.2.2.2.2.2.1
  have change := legal.2.2.2.2.2.2.2.2.1
  unfold netAmount
  omega

inductive Context
  | ordinary
  | fee
  deriving DecidableEq

structure VolumeWitness where
  context : Context
  regulated : Bool
  external : Bool
  useReal : Bool
  startsNewDay : Bool
  prior : Nat
  outbound : Nat
  successor : Nat
  limit : Nat
  timestamp : Nat
  dayIndex : Nat
  second : Nat
  publishedDayStart : Nat

def eligible (w : VolumeWitness) : Bool :=
  w.context == .ordinary && w.regulated && w.external

def disclosed (w : VolumeWitness) : Bool := eligible w && !w.useReal

/-- Candidate range is unconditional, including disclosed/self/fee branches.
Origin/continuation commitments and replay state require separate equations. -/
def VolumeArithmeticIntent (w : VolumeWitness) : Prop :=
  w.prior < amountBound ∧ w.outbound < amountBound ∧
  w.successor < amountBound ∧ w.limit < amountBound ∧
  w.prior + w.outbound < amountBound ∧
  w.timestamp < 2 ^ 64 ∧ w.dayIndex < 2 ^ 48 ∧ w.second < 86400 ∧
  w.timestamp = w.dayIndex * 86400 + w.second ∧
  w.publishedDayStart = (if w.context = .ordinary then w.dayIndex * 86400 else 0) ∧
  (w.useReal = true → eligible w = true ∧ w.successor = w.prior + w.outbound ∧
    w.successor ≤ w.limit ∧ (w.startsNewDay = true → w.prior = 0)) ∧
  (w.external = true → w.context = .ordinary)

/-- An undisclosed accumulator transition adds outbound; disclosure preserves
the prior accumulator head. This models policy intent, not Rust state refinement. -/
inductive VolumeStep (limit : Nat) : Nat → Nat → Prop
  | tracked (prior outbound : Nat) (within : prior + outbound ≤ limit) :
      VolumeStep limit prior (prior + outbound)
  | disclosure (prior : Nat) : VolumeStep limit prior prior

inductive VolumeTrace (limit : Nat) : Nat → Nat → Prop
  | nil (start : Nat) : VolumeTrace limit start start
  | next {start prior final : Nat} (priorTrace : VolumeTrace limit start prior)
      (step : VolumeStep limit prior final) : VolumeTrace limit start final

theorem volume_step_preserves_limit {limit prior final : Nat}
    (bounded : prior ≤ limit) (step : VolumeStep limit prior final) : final ≤ limit := by
  cases step with
  | tracked _ within => exact within
  | disclosure => exact bounded

/-- Unbounded ABSTRACT undisclosed-volume invariant. Authentication, unique
origin, predecessor consumption and current Rust storage are not hypotheses here
because this theorem does not establish their refinement into VolumeTrace. -/
theorem volume_trace_preserves_limit {limit start final : Nat}
    (bounded : start ≤ limit) (trace : VolumeTrace limit start final) : final ≤ limit := by
  induction trace with
  | nil => exact bounded
  | next _ step ih => exact volume_step_preserves_limit ih step

theorem disclosure_preserves_accumulator (limit prior : Nat) :
    VolumeStep limit prior prior := .disclosure prior

theorem inclusive_endpoint (limit : Nat) : VolumeStep limit 0 limit := by
  simpa using VolumeStep.tracked (limit := limit) 0 limit (by omega)



end ShielddSecurity.TransferCore

set_option pp.all true in
#check @ShielddSecurity.TransferCore.amountBound
#print axioms ShielddSecurity.TransferCore.amountBound
set_option pp.all true in
#check @ShielddSecurity.TransferCore.fieldModulus
#print axioms ShielddSecurity.TransferCore.fieldModulus
set_option pp.all true in
#check @ShielddSecurity.TransferCore.scalarOrder
#print axioms ShielddSecurity.TransferCore.scalarOrder
set_option pp.all true in
#check @ShielddSecurity.TransferCore.Affine
#print axioms ShielddSecurity.TransferCore.Affine
set_option pp.all true in
#check @ShielddSecurity.TransferCore.Address
#print axioms ShielddSecurity.TransferCore.Address
set_option pp.all true in
#check @ShielddSecurity.TransferCore.CanonicalAffine
#print axioms ShielddSecurity.TransferCore.CanonicalAffine
set_option pp.all true in
#check @ShielddSecurity.TransferCore.Note
#print axioms ShielddSecurity.TransferCore.Note
set_option pp.all true in
#check @ShielddSecurity.TransferCore.RealSpend
#print axioms ShielddSecurity.TransferCore.RealSpend
set_option pp.all true in
#check @ShielddSecurity.TransferCore.DummySpend
#print axioms ShielddSecurity.TransferCore.DummySpend
set_option pp.all true in
#check @ShielddSecurity.TransferCore.OptionalSpend
#print axioms ShielddSecurity.TransferCore.OptionalSpend
set_option pp.all true in
#check @ShielddSecurity.TransferCore.OptionalSpend.amount
#print axioms ShielddSecurity.TransferCore.OptionalSpend.amount
set_option pp.all true in
#check @ShielddSecurity.TransferCore.Witness
#print axioms ShielddSecurity.TransferCore.Witness
set_option pp.all true in
#check @ShielddSecurity.TransferCore.RealInputIntent
#print axioms ShielddSecurity.TransferCore.RealInputIntent
set_option pp.all true in
#check @ShielddSecurity.TransferCore.OptionalInputIntent
#print axioms ShielddSecurity.TransferCore.OptionalInputIntent
set_option pp.all true in
#check @ShielddSecurity.TransferCore.CoreIntent
#print axioms ShielddSecurity.TransferCore.CoreIntent
set_option pp.all true in
#check @ShielddSecurity.TransferCore.netAmount
#print axioms ShielddSecurity.TransferCore.netAmount
set_option pp.all true in
#check @ShielddSecurity.TransferCore.signedResidue
#print axioms ShielddSecurity.TransferCore.signedResidue
set_option pp.all true in
#check @ShielddSecurity.TransferCore.optional_amount_bounded
#print axioms ShielddSecurity.TransferCore.optional_amount_bounded
set_option pp.all true in
#check @ShielddSecurity.TransferCore.net_amount_bounded
#print axioms ShielddSecurity.TransferCore.net_amount_bounded
set_option pp.all true in
#check @ShielddSecurity.TransferCore.Context
#print axioms ShielddSecurity.TransferCore.Context
set_option pp.all true in
#check @ShielddSecurity.TransferCore.VolumeWitness
#print axioms ShielddSecurity.TransferCore.VolumeWitness
set_option pp.all true in
#check @ShielddSecurity.TransferCore.eligible
#print axioms ShielddSecurity.TransferCore.eligible
set_option pp.all true in
#check @ShielddSecurity.TransferCore.disclosed
#print axioms ShielddSecurity.TransferCore.disclosed
set_option pp.all true in
#check @ShielddSecurity.TransferCore.VolumeArithmeticIntent
#print axioms ShielddSecurity.TransferCore.VolumeArithmeticIntent
set_option pp.all true in
#check @ShielddSecurity.TransferCore.VolumeStep
#print axioms ShielddSecurity.TransferCore.VolumeStep
set_option pp.all true in
#check @ShielddSecurity.TransferCore.VolumeTrace
#print axioms ShielddSecurity.TransferCore.VolumeTrace
set_option pp.all true in
#check @ShielddSecurity.TransferCore.volume_step_preserves_limit
#print axioms ShielddSecurity.TransferCore.volume_step_preserves_limit
set_option pp.all true in
#check @ShielddSecurity.TransferCore.volume_trace_preserves_limit
#print axioms ShielddSecurity.TransferCore.volume_trace_preserves_limit
set_option pp.all true in
#check @ShielddSecurity.TransferCore.disclosure_preserves_accumulator
#print axioms ShielddSecurity.TransferCore.disclosure_preserves_accumulator
set_option pp.all true in
#check @ShielddSecurity.TransferCore.inclusive_endpoint
#print axioms ShielddSecurity.TransferCore.inclusive_endpoint
