import ShielddSecurity.MerkleQuaternary30
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.ReusablePoseidonPhase31
open Compiler CompilerCompletion CompilerIndexed01 CompilerSegmentCompletion11 Poseidon
open CapturedInitial73419Generic01

/-- Computational input only: no row truth, desired hash, or proof in a state recipe. -/
structure Data (width : Nat) where
  parameters : Parameters Int width
  index : Nat
  low : Nat
  high : Nat
  before : State Linear width
  shifted : State Linear width
  transformed : State Linear width
  after : State Linear width
  rows : List Row
  pivots : Fin width → Option Nat
  rowStarts : Fin width → Nat
  coefficients : Fin width → Int

def laneSteps (input : Linear) (column : Nat) : List Step :=
  [.square input [] column,.square [(column,1)] [] (column+1),
   .product [(column+1,1)] input [] (column+2) (column+3)]
def materialized {width : Nat} (d : Data width) : List Step :=
  (List.finRange width).flatMap (fun i => match d.pivots i with
    | none => []
    | some column => laneSteps (d.shifted i) column)
def steps {width : Nat} (d : Data width) := materialized d++[TransferPoseidonCall04Shared01.copyStep]
def hints {width : Nat} (d : Data width) (i : Fin width) : PoseidonIndexedFolded02.FifthHint :=
  match d.pivots i with
  | none => .constant (d.coefficients i)
  | some column =>
    let row := d.rowStarts i
    .arithmetic ⟨[(column,1)],[(column+1,1)],[(column+3,1)],row,row+1,row+2,row+3⟩

/-- Every field is an independently checked finite syntax/order/coverage obligation. -/
structure Certificate {width : Nat} (d : Data width) : Prop where
  phase : PoseidonIndexedFolded02.checkRound p copy d.rows.toArray d.parameters d.index
    d.before d.shifted d.transformed d.after (hints d)=true
  order : CompilerOrder.checkOrder [0,copy] [] (steps d)=true
  coverage : checkOriginalCoverage p copy d.rows.toArray (emitted (steps d)).toArray
    (List.range d.rows.length).toArray=true
  writes : writeCheck d.low d.high (steps d)=true
  support : supportCheck d.high d.rows=true
  copyLink : checkRow p d.rows ⟨[(0,1),(copy,-1)],[]⟩=true

variable {F : Type} [Field F]
theorem lane_legal (base : Nat → F) (input : Linear) (column : Nat) : Legal base (laneSteps input column) := by
  simp [laneSteps,Legal,Step.Legal]
theorem legal_flatmap {α : Type} (items : List α) (program : α → List Step)
    (each : ∀ item,∀ base : Nat → F, Legal base (program item)) : ∀ base : Nat → F,Legal base (items.flatMap program) := by
  induction items with
  | nil => intro base; simp [Legal]
  | cons item items ih =>
    intro base
    exact PoseidonCallComposition04.legal_append base (program item) (items.flatMap program) (each item base) (ih (run base (program item)))
theorem legal {width : Nat} (d : Data width) (base : Nat → F) : Legal base (steps d) := by
  apply PoseidonCallComposition04.legal_append
  · apply legal_flatmap
    intro i current
    cases pivot : d.pivots i with
    | none => simp [Legal]
    | some column => simpa [pivot] using lane_legal current (d.shifted i) column
  · simp [TransferPoseidonCall04Shared01.copyStep,Legal,Step.Legal]

variable [CharP F p]
theorem complete {width : Nat} (d : Data width) (checked : Certificate d) (base : Nat → F)
    (linked : base copy=base 0) : Satisfies (run base (steps d)) d.rows :=
  (original_rows_complete base (steps d) [0,copy] d.rows copy
    (CompilerOrder.checked_order _ _ _ checked.order) (legal d base) (by simp) (by simp)
    linked (checkOriginalCoverage_sound p copy _ _ _ checked.coverage)).1
def segment {width : Nat} (d : Data width) (checked : Certificate d) : Segment F copy :=
  makeSegment (steps d) d.rows d.low d.high checked.writes checked.support (complete d checked)
theorem outside {width : Nat} (d : Data width) (checked : Certificate d) (base : Nat → F)
    (column : Nat) (bound : column<d.low ∨ d.high≤column) : run base (steps d) column=base column :=
  CompilerSegmentCompletion11.outside copy (segment (F:=F) d checked) base column bound
theorem arbitrary_round {width : Nat} (d : Data width) (checked : Certificate d) (rho : Nat → F)
    (one : rho 0=1) (sat : Satisfies rho d.rows) :
    (fun i => eval rho (d.after i))=Poseidon.round (castParameters d.parameters) d.index (fun i => eval rho (d.before i)) :=
  round_certificate_sound rho _ d.parameters d.index d.before d.shifted d.transformed d.after one
    MerkleHash27R0Proof.four_ne_zero (unoutline_rows_sound rho copy d.rows sat checked.copyLink)
    (PoseidonIndexedFolded02.checkRound_sound p copy _ d.parameters d.index d.before d.shifted d.transformed d.after (hints d) checked.phase)
theorem prior_frame {width : Nat} (d : Data width) (checked : Certificate d) (base : Nat → F)
    (rows : List Row) (sat : Satisfies base rows)
    (support : ∀ row∈rows,∀ term∈row.a++row.b,term.1<d.low ∨ d.high≤term.1) :
    Satisfies (run base (steps d)) rows :=
  CompilerSegmentCompletion11.prior_preserved copy (segment (F:=F) d checked) base rows sat support
end ShielddSecurity.ReusablePoseidonPhase31

set_option pp.all true in
#check @ShielddSecurity.ReusablePoseidonPhase31.Data
#print axioms ShielddSecurity.ReusablePoseidonPhase31.Data
set_option pp.all true in
#check @ShielddSecurity.ReusablePoseidonPhase31.laneSteps
#print axioms ShielddSecurity.ReusablePoseidonPhase31.laneSteps
set_option pp.all true in
#check @ShielddSecurity.ReusablePoseidonPhase31.materialized
#print axioms ShielddSecurity.ReusablePoseidonPhase31.materialized
set_option pp.all true in
#check @ShielddSecurity.ReusablePoseidonPhase31.steps
#print axioms ShielddSecurity.ReusablePoseidonPhase31.steps
set_option pp.all true in
#check @ShielddSecurity.ReusablePoseidonPhase31.hints
#print axioms ShielddSecurity.ReusablePoseidonPhase31.hints
set_option pp.all true in
#check @ShielddSecurity.ReusablePoseidonPhase31.Certificate
#print axioms ShielddSecurity.ReusablePoseidonPhase31.Certificate
set_option pp.all true in
#check @ShielddSecurity.ReusablePoseidonPhase31.lane_legal
#print axioms ShielddSecurity.ReusablePoseidonPhase31.lane_legal
set_option pp.all true in
#check @ShielddSecurity.ReusablePoseidonPhase31.legal_flatmap
#print axioms ShielddSecurity.ReusablePoseidonPhase31.legal_flatmap
set_option pp.all true in
#check @ShielddSecurity.ReusablePoseidonPhase31.legal
#print axioms ShielddSecurity.ReusablePoseidonPhase31.legal
set_option pp.all true in
#check @ShielddSecurity.ReusablePoseidonPhase31.complete
#print axioms ShielddSecurity.ReusablePoseidonPhase31.complete
set_option pp.all true in
#check @ShielddSecurity.ReusablePoseidonPhase31.segment
#print axioms ShielddSecurity.ReusablePoseidonPhase31.segment
set_option pp.all true in
#check @ShielddSecurity.ReusablePoseidonPhase31.outside
#print axioms ShielddSecurity.ReusablePoseidonPhase31.outside
set_option pp.all true in
#check @ShielddSecurity.ReusablePoseidonPhase31.arbitrary_round
#print axioms ShielddSecurity.ReusablePoseidonPhase31.arbitrary_round
set_option pp.all true in
#check @ShielddSecurity.ReusablePoseidonPhase31.prior_frame
#print axioms ShielddSecurity.ReusablePoseidonPhase31.prior_frame
