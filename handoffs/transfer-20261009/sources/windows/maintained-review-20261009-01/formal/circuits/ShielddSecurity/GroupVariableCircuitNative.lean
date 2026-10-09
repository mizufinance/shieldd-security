import ShielddSecurity.GroupVariableCircuitCompletion
import ShielddSecurity.TransferOwnership
import ShielddSecurity.GroupNativeMultiply

set_option maxHeartbeats 300000

namespace ShielddSecurity.GroupVariableCircuitNative

open GroupFixedCircuitCompletion
open GroupVariableCircuitCompletion
variable {F J : Type} [Field F] [AddCommGroup J]

/-- Every actual local renderer must prove this universal arithmetic statement
from its constructed product and quotient rows. It is not an input-specific
native endpoint assumption. The shared native table association is separate. -/
def LocalFormula (d : F) (copy : Nat) (tables : Tables) (program : Program) : Prop :=
  ∀ rho : Nat → F, rho 0 = 1 → rho copy = rho 0 →
    Group.OnCurve d (point rho program.input) → Curved d tables rho →
    eval rho program.low = (if program.lowBit then 1 else 0) →
    eval rho program.high = (if program.highBit then 1 else 0) →
    point (program.build rho) program.output = Group.affineAdd d
      (Group.affineAdd d (Group.affineAdd d (point rho program.input) (point rho program.input))
        (Group.affineAdd d (point rho program.input) (point rho program.input)))
      (Group.windowPoint (eval rho program.low) (eval rho program.high)
        (point rho tables.base) (point rho tables.twice) (point rho tables.triple))

def pairs (programs : List Program) : List (Bool × Bool) :=
  programs.map (fun program => (program.lowBit,program.highBit))

def nativeValue (base : J) (programs : List Program) (acc : J) : J :=
  (pairs programs).foldl (fun value pair =>
    4 • value + GroupNativeMultiply.pairDigit pair • base) acc

theorem affine_identity_left (d : F) (right : Group.Point F) :
    Group.affineAdd d Group.identityPoint right = right := by
  cases right
  simp [Group.affineAdd,Group.cross,Group.diagonal,Group.delta,Group.identityPoint]

theorem affine_window_native (d : F) (model : Group.StandardCurveModel J d)
    (base acc : J) (low high : Bool) :
    Group.affineAdd d
      (Group.affineAdd d (Group.affineAdd d (model.coordinates acc) (model.coordinates acc))
        (Group.affineAdd d (model.coordinates acc) (model.coordinates acc)))
      (Group.windowPoint (if low then 1 else 0) (if high then 1 else 0)
        (model.coordinates base) (model.coordinates (2 • base)) (model.coordinates (3 • base))) =
      model.coordinates (4 • acc + (low.toNat + 2 * high.toNat) • base) := by
  have double (value : J) : Group.affineAdd d (model.coordinates value) (model.coordinates value) =
      model.coordinates (2 • value) := by
    rw [two_nsmul,model.addition]
  simp only [double,TransferOwnership.selected_coordinates d model base low high]
  rw [← model.addition]
  congr 1
  simp only [← mul_nsmul]

/-- The accumulator invariant is derived by list induction from universal
local formula proofs and exact write exclusion. No final native coordinate,
nonidentity, inverse, row satisfaction or scalar value is supplied. -/
theorem run_coordinates (d : F) (copy : Nat) (model : Group.StandardCurveModel J d)
    (base acc : J) (rho : Nat → F) (tables : Tables) (programs : List Program)
    (input : Linear × Linear) (kept : List Nat)
    (formulas : ∀ program ∈ programs, LocalFormula d copy tables program)
    (protection : ∀ program ∈ programs, Protected kept program)
    (tableSupports : ∀ term ∈ tables.terms, term.1 ∈ kept)
    (bitSupports : ∀ program ∈ programs, ∀ term ∈ program.low ++ program.high, term.1 ∈ kept)
    (alignment : Aligned input programs) (oneKept : 0 ∈ kept) (copyKept : copy ∈ kept)
    (one : rho 0 = 1) (linked : rho copy = rho 0)
    (incoming : point rho input = model.coordinates acc)
    (baseTable : point rho tables.base = model.coordinates base)
    (twiceTable : point rho tables.twice = model.coordinates (2 • base))
    (tripleTable : point rho tables.triple = model.coordinates (3 • base))
    (bits : ∀ program ∈ programs,
      eval rho program.low = (if program.lowBit then 1 else 0) ∧
      eval rho program.high = (if program.highBit then 1 else 0)) :
    point (run rho programs) (output input programs) = model.coordinates (nativeValue base programs acc) := by
  induction programs generalizing acc rho input with
  | nil => simpa only [run,output,nativeValue,pairs,List.map_nil,List.foldl_nil] using incoming
  | cons program tail ih =>
      have current : point rho program.input = model.coordinates acc := by
        rw [alignment.1]
        exact incoming
      have curved : Curved d tables rho := by
        unfold Curved
        rw [baseTable,twiceTable,tripleTable]
        exact ⟨model.onCurve base,model.onCurve (2 • base),model.onCurve (3 • base)⟩
      have currentCurve : Group.OnCurve d (point rho program.input) := by
        rw [current]
        exact model.onCurve acc
      have currentBits := bits program (by simp)
      have coordinates := formulas program (by simp) rho one linked currentCurve curved
        currentBits.1 currentBits.2
      rw [current,currentBits.1,currentBits.2,baseTable,twiceTable,tripleTable] at coordinates
      have next := coordinates.trans (affine_window_native d model base acc program.lowBit program.highBit)
      have preserves (column : Nat) (member : column ∈ kept) : program.build rho column = rho column :=
        GroupCircuitOrder.run_outside rho program.stages column
          (by intro stage present; exact protection program (by simp) stage present column member)
      have oneBuilt : program.build rho 0 = 1 := (preserves 0 oneKept).trans one
      have linkedBuilt : program.build rho copy = program.build rho 0 := by
        rw [preserves copy copyKept,preserves 0 oneKept,linked]
      have unchanged := table_preserved rho program tables kept (protection program (by simp)) tableSupports
      have remainingBits : ∀ next ∈ tail,
          eval (program.build rho) next.low = (if next.lowBit then 1 else 0) ∧
          eval (program.build rho) next.high = (if next.highBit then 1 else 0) := by
        intro next member
        have present := List.mem_cons_of_mem program member
        have values := bits next present
        have agrees (terms : Linear) (inside : ∀ term ∈ terms, term ∈ next.low ++ next.high) :
            eval (program.build rho) terms = eval rho terms := by
          apply eval_agrees
          intro term member
          exact preserves term.1 (bitSupports next present term (inside term member))
        exact ⟨(agrees next.low (by intro term member; exact List.mem_append_left next.high member)).trans values.1,
          (agrees next.high (by intro term member; exact List.mem_append_right next.low member)).trans values.2⟩
      have result := ih (4 • acc + (program.lowBit.toNat + 2 * program.highBit.toNat) • base)
        (program.build rho) program.output
        (by intro next member; exact formulas next (List.mem_cons_of_mem program member))
        (by intro next member; exact protection next (List.mem_cons_of_mem program member))
        (by intro next member; exact bitSupports next (List.mem_cons_of_mem program member))
        alignment.2 oneBuilt linkedBuilt next (unchanged.1.trans baseTable)
        (unchanged.2.1.trans twiceTable) (unchanged.2.2.trans tripleTable) remainingBits
      simpa only [run,output,nativeValue,pairs,List.map_cons,List.foldl_cons,
        GroupNativeMultiply.pairDigit] using result

/-- A checked exact reversed pair order connects the native fold to the
written binary magnitude, including odd-width false padding. -/
theorem scalar_coordinates (d : F) (copy : Nat) (model : Group.StandardCurveModel J d)
    (base : J) (rho : Nat → F) (tables : Tables) (programs : List Program)
    (input : Linear × Linear) (kept : List Nat) (writtenBits : List Bool)
    (formulas : ∀ program ∈ programs, LocalFormula d copy tables program)
    (protection : ∀ program ∈ programs, Protected kept program)
    (tableSupports : ∀ term ∈ tables.terms, term.1 ∈ kept)
    (bitSupports : ∀ program ∈ programs, ∀ term ∈ program.low ++ program.high, term.1 ∈ kept)
    (alignment : Aligned input programs) (oneKept : 0 ∈ kept) (copyKept : copy ∈ kept)
    (one : rho 0 = 1) (linked : rho copy = rho 0)
    (incoming : point rho input = model.coordinates 0)
    (baseTable : point rho tables.base = model.coordinates base)
    (twiceTable : point rho tables.twice = model.coordinates (2 • base))
    (tripleTable : point rho tables.triple = model.coordinates (3 • base))
    (bits : ∀ program ∈ programs,
      eval rho program.low = (if program.lowBit then 1 else 0) ∧
      eval rho program.high = (if program.highBit then 1 else 0))
    (pairOrder : pairs programs = (GroupNativeMultiply.pairBits writtenBits).reverse) :
    point (run rho programs) (output input programs) =
      model.coordinates (ShielddSecurity.binary writtenBits • base) := by
  have result := run_coordinates d copy model base 0 rho tables programs input kept formulas protection
    tableSupports bitSupports alignment oneKept copyKept one linked incoming baseTable twiceTable tripleTable bits
  unfold nativeValue at result
  rw [pairOrder,GroupNativeMultiply.pair_loop_value] at result
  exact result

set_option pp.all true in
#check @affine_identity_left
#print axioms affine_identity_left
set_option pp.all true in
#check @affine_window_native
#print axioms affine_window_native
set_option pp.all true in
#check @run_coordinates
#print axioms run_coordinates
set_option pp.all true in
#check @scalar_coordinates
#print axioms scalar_coordinates

end ShielddSecurity.GroupVariableCircuitNative
