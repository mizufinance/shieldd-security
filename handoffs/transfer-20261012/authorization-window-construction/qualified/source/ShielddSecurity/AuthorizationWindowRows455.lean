import ShielddSecurity.AuthorizationTraceLocal453
import ShielddSecurity.VariableTraceBitIndex454
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationWindowRows455
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open AuthorizationTraceIndex450 AuthorizationTraceSeed451

def family (index : Nat) : VariableWindowLayout447.Family := ⟨1504+16*index,2253+756*index,2257+758*index⟩

def Complete (bound : VariableWindowLayout447.BoundEntry) : Prop :=
  VariableWindowLayout447.checkBound bound=true ∧
  VariableWindowJoin443.check bound.entry=true ∧
  VariableOperationAdapter434.check bound.entry.first=true ∧
  VariableOperationAdapter434.check bound.entry.second=true ∧
  VariableOperationAdapter434.check bound.entry.addition=true ∧
  VariableSelectorAdapter437.check bound.entry.selector=true
noncomputable instance completeDecidable (bound : VariableWindowLayout447.BoundEntry) : Decidable (Complete bound) := by
  unfold Complete;infer_instance
noncomputable def check (bound : VariableWindowLayout447.BoundEntry) : Bool := decide (Complete bound)

theorem local_rows (original rho : Nat → F) (bases : Nat → curve.Point) (scalar index window : Nat)
    (familyBound : index<2) (e : VariableWindowJoin443.Entry)
    (checked : check ⟨family index,window,e⟩=true)
    (one : rho copy=1) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (base : VariableWindowColumns449.columnPoint rho (1504+16*index)=model.coordinates (bases index))
    (hints : ∀ column,2253≤column → column≤3764 → rho column=seed original bases scalar column)
    (lowBit : rho (2250-2*window)=if (encodeBits 252 scalar)[250-2*window]?.getD false then 1 else 0)
    (highBit : rho (2251-2*window)=if (encodeBits 252 scalar)[251-2*window]?.getD false then 1 else 0) :
    VariableWindowJoin443.Rows rho e := by
  have facts : Complete ⟨family index,window,e⟩ := of_decide_eq_true checked
  rcases facts with ⟨layout,wiring,first,second,addition,selector⟩
  have valid : VariableWindowLayout447.Valid (family index) window e := of_decide_eq_true layout
  have lower := valid.1
  have upper := valid.2.1
  have bitPair := VariableTraceBitIndex454.windows_bits model (bases index) (encodeBits 252 scalar)
    (by simp) empty window upper
  change ((windowAt (bases index) scalar window).low,(windowAt (bases index) scalar window).high)=_ at bitPair
  have low := congrArg Prod.fst bitPair
  have high := congrArg Prod.snd bitPair
  change (windowAt (bases index) scalar window).low=(encodeBits 252 scalar)[250-2*window]?.getD false at low
  change (windowAt (bases index) scalar window).high=(encodeBits 252 scalar)[251-2*window]?.getD false at high
  have lowValue : rho (2250-2*window)=if (windowAt (bases index) scalar window).low then 1 else 0 := by
    rw [low];exact lowBit
  have highValue : rho (2251-2*window)=if (windowAt (bases index) scalar window).high then 1 else 0 := by
    rw [high];exact highBit
  apply (VariableWindowColumns449.equations_iff (family index) window e layout wiring first second addition selector
    rho one arithmetic (windowAt (bases index) scalar window).low (windowAt (bases index) scalar window).high lowValue highValue).mpr
  have pointHints (col : Nat) (lowerCol : 2253≤col) (upperCol : col≤3763) :
      VariableWindowColumns449.columnPoint rho col=VariableWindowColumns449.columnPoint (seed original bases scalar) col := by
    unfold VariableWindowColumns449.columnPoint
    rw [hints col lowerCol (by omega),hints (col+1) (by omega) (by omega)]
  have precompute : (family index).precomputeX=column index 0 0 0 := by simp [family,column]
  have triple : (family index).precomputeX+2=column index 0 1 0 := by simp [family,column]
  have prev : VariableWindowLayout447.previous (family index) window=column index (window-1) 2 0 := by
    dsimp only [VariableWindowLayout447.previous,family,column];omega
  have firstCol : VariableWindowLayout447.previous (family index) window+2=column index window 0 0 := by
    dsimp only [VariableWindowLayout447.previous,family,column];omega
  have secondCol : VariableWindowLayout447.previous (family index) window+4=column index window 1 0 := by
    dsimp only [VariableWindowLayout447.previous,family,column];omega
  have outputCol : VariableWindowLayout447.previous (family index) window+6=column index window 2 0 := by
    dsimp only [VariableWindowLayout447.previous,family,column];omega
  have baseColumn : VariableWindowColumns449.columnPoint rho (family index).baseX=model.coordinates (bases index) := base
  rw [baseColumn]
  unfold VariableWindowColumns449.witness
  rw [triple,precompute,firstCol,secondCol,outputCol,prev]
  rw [pointHints (column index 0 0 0) (by unfold column;omega) (by unfold column;omega)]
  rw [pointHints (column index 0 1 0) (by unfold column;omega) (by unfold column;omega)]
  rw [pointHints (column index (window-1) 2 0) (by unfold column;omega) (by unfold column;omega)]
  rw [pointHints (column index window 0 0) (by unfold column;omega) (by unfold column;omega)]
  rw [pointHints (column index window 1 0) (by unfold column;omega) (by unfold column;omega)]
  rw [pointHints (column index window 2 0) (by unfold column;omega) (by unfold column;omega)]
  exact AuthorizationTraceLocal453.seed_equations original bases scalar index window familyBound lower upper
end ShielddSecurity.AuthorizationWindowRows455

set_option pp.all true in
#check @ShielddSecurity.AuthorizationWindowRows455.family
#print axioms ShielddSecurity.AuthorizationWindowRows455.family

set_option pp.all true in
#check @ShielddSecurity.AuthorizationWindowRows455.Complete
#print axioms ShielddSecurity.AuthorizationWindowRows455.Complete

set_option pp.all true in
#check @ShielddSecurity.AuthorizationWindowRows455.completeDecidable
#print axioms ShielddSecurity.AuthorizationWindowRows455.completeDecidable

set_option pp.all true in
#check @ShielddSecurity.AuthorizationWindowRows455.check
#print axioms ShielddSecurity.AuthorizationWindowRows455.check

set_option pp.all true in
#check @ShielddSecurity.AuthorizationWindowRows455.local_rows
#print axioms ShielddSecurity.AuthorizationWindowRows455.local_rows
