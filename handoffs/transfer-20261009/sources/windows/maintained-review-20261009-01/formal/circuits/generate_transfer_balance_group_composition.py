"""Same-assignment signed/variable65/H126/final owned-row composition.

Only genuine qualified parents and the retained ONE joint replay are accepted.
The native SDK asset point and named global VALUE_BLINDING generator binding
remain source/model contracts. Earlier asset-map seed reuse and the production
native balance/encoding association remain separate joins, not wanted outputs.
"""
from . import transfer_balance_native_composition as frames
from . import transfer_balance_variable_program as variable
from . import transfer_balance_blinding_program as blinding
from . import transfer_balance_final_add as final
from . import transfer_remaining_pages as remaining
from . import generate_transfer_balance_variable_sequence as sequence
from . import generate_transfer_balance_final_add_completion as addition
from . import transfer_relation as relation
from .generate_hash_round import _signature_audits
from . import transfer_balance_input_layout as layout


def _fence(support,writes,origin=22738,copy=200692):
    if any(column!=copy and not 0<=column<copy for column in support):
        raise relation.RelationError('balance group prior supports outside actual two allocation regions')
    low=max((column for column in support if column<origin),default=-1)+1
    high=max((column for column in support if origin<=column<copy),default=origin-1)+1
    covered=lambda column:column<low or origin<=column<high or column==copy
    exceptions=sorted(column for column in writes if covered(column))
    if len(exceptions)>64 or set(exceptions)&support:
        raise relation.RelationError('balance group bounded exact write exceptions/earlier support')
    return dict(low=low,high=high,exceptions=exceptions)


def generate(vparent,vpages,bparent,bpages,cparent,cpage,roles,signed,asset_base,blinding_base,joint,readonly_lcs=()):
    exact=frames.plan(vparent,vpages,bparent,bpages,cparent,cpage,roles,signed,asset_base,blinding_base,joint,readonly_lcs)
    v=variable.plan(vparent,vpages,final.DIGEST,signed,asset_base,joint['variable'],readonly_lcs)
    caller=remaining.inspect_page(cparent,cpage,0,roles)
    scalar=caller['records']['caller','shared',0][6]
    b=blinding.plan(bparent,bpages,blinding_base,scalar,joint['blinding'],readonly_lcs)
    f=joint['final_add'];addition._recheck(f)
    sequence._kept(v,signed)
    # Source Witness6 lowers to shadow9. Its independent committed target2 is
    # linked by the actual compiler assertion constructed before every gadget.
    if b['canonical']['value']!=9:
        raise relation.RelationError('balance group actual committed native blinding shadow9')
    layout.render(joint['input_layout'])
    rows=frames._rows([*v['selections'],joint['blinding']['canonical']['certificate'],joint['blinding']['fixed'],
        joint['input_layout'],{'selected_rows':f['selected_rows']},{'selected_rows':signed['raw_rows']}])
    signed_support={column for row in signed['raw_rows'] for side in ('a','b') for column,_ in row[side]}
    vr=set(v['rows']);br=set(b['loop']['rows'])|set(b['canonical']['rows'])
    before_h=signed_support|{2,9}|frames._support(rows,vr)
    before_final=before_h|frames._support(rows,br)
    hw=set(b['canonical']['writes'])|set(b['loop']['writes'])
    if hw&signed_support or set(f['writes'])&signed_support:
        raise relation.RelationError('balance group H/final destroys independently constructed signed135 rows')
    hframe=_fence(before_h,hw);fframe=_fence(before_final,set(f['writes']))
    return _render(exact,v,b,f,signed,hframe,fframe)


def _render(exact,v,b,f,signed,hframe,fframe):
    V='RuntimeBalanceVariableSequence';S='RuntimeTransferSignedBalanceCompletion'
    H='RuntimeBalanceBlindingFixedCompletion';A='RuntimeBalanceBlindingFixed'
    B='RuntimeBalanceBlindingCanonical';N='RuntimeBalanceBlindingNativeScalar'
    HF='RuntimeBalanceBlindingFixedFrame';F='RuntimeTransferBalanceFinalAddCompletion'
    L='RuntimeBalanceInputLayout'
    T='RuntimeBalanceVariableWindow000NativePrecompute';D='RuntimeBalanceVariableWindow000Point0Cones'
    name='RuntimeBalanceGroupComposition'
    P=[f'RuntimeBalanceVariableWindow{i:03d}Program' for i in range(65)]
    start=signed['bits'][0];neg=signed['negative'];copy=signed['copy']
    source=f'''import ShielddSecurity.{V}Signed
import ShielddSecurity.{N}
import ShielddSecurity.{HF}
import ShielddSecurity.{F}
import ShielddSecurity.{L}
import ShielddSecurity.GroupFrameExceptions
import ShielddSecurity.GroupSignedPoint
namespace ShielddSecurity.{name}
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
-- Real qualified parents and original row identity {exact['identity']['relation_digest']}.
-- Native asset object/source and same-map seed reuse are independent joins.
def hFrame : GroupFixedCircuitBounds.Frame := ⟨{hframe['low']},{hframe['high']}⟩
def finalFrame : GroupFixedCircuitBounds.Frame := ⟨{fframe['low']},{fframe['high']}⟩
def hExceptions : List Nat := {hframe['exceptions']}
def finalExceptions : List Nat := {fframe['exceptions']}
def signedVariableRows (n : Nat) : List Row := {L}.rawRows ++ ({S}.rawRows ++ {V}.ownedRows n)
def priorRows (n : Nat) : List Row := signedVariableRows n ++ {A}.rawRows
def ownedRows (n : Nat) : List Row := priorRows n ++ {F}.rawRows
theorem h_writes_checked (b : Nat) :
    GroupFrameExceptions.checkWrites 22738 {copy} hFrame hExceptions ({HF}.ownedWrites b) = true := by
  change GroupFrameExceptions.checkWrites 22738 {copy} hFrame hExceptions ({HF}.ownedWrites 0) = true
  decide
theorem h_rows_checked (n : Nat) :
    GroupFrameExceptions.checkRows 22738 {copy} hFrame hExceptions (signedVariableRows n) = true := by
  change GroupFrameExceptions.checkRows 22738 {copy} hFrame hExceptions (signedVariableRows 0) = true
  decide
theorem final_writes_checked :
    GroupFrameExceptions.checkWrites 22738 {copy} finalFrame finalExceptions {F}.ownedWrites = true := by decide
theorem final_rows_checked (n : Nat) :
    GroupFrameExceptions.checkRows 22738 {copy} finalFrame finalExceptions (priorRows n) = true := by
  change GroupFrameExceptions.checkRows 22738 {copy} finalFrame finalExceptions (priorRows 0) = true
  decide
variable {{E SdkPoint R K Q Signing J Encoded Native Fld : Type}}
variable [Field Fld] [DecidableEq Fld] [CharP Fld Scalar.modulus] [AddCommGroup J]
variable (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
variable (model : Group.StandardCurveModel J ({D}.coefficientD : Fld))
variable (upstream : ShielddNativeSdk.Upstream E SdkPoint R K Q Signing J fq fr ({D}.coefficientD : Fld) model)
variable (backend : ShielddScalarReader.Backend (F := Fld) Encoded Native)
variable (assetPoint : SdkPoint) (base : Nat → Fld)
def unsignedAssignment (amounts : TransferSignedMagnitude.Inputs) : Nat → Fld :=
  {V}.construct fq fr model upstream backend assetPoint ({S}.completeAssignment ({L}.construct base) amounts)
    (TransferSignedMagnitude.magnitude amounts)
def blindedAssignment (amounts : TransferSignedMagnitude.Inputs) (b : Nat) : Nat → Fld :=
  {H}.construct (unsignedAssignment fq fr model upstream backend assetPoint base amounts) b
def construct (amounts : TransferSignedMagnitude.Inputs) (b : Nat) : Nat → Fld :=
  {F}.completeAssignment (blindedAssignment fq fr model upstream backend assetPoint base amounts b)
def ownedWrites (n b : Nat) : List Nat :=
  [9] ++ ({S}.writes ++ ({V}.ownedWrites n ++ ({HF}.ownedWrites b ++ {F}.ownedWrites)))
theorem outside_column (amounts : TransferSignedMagnitude.Inputs) (b column : Nat)
    (excluded : column ∉ ownedWrites (TransferSignedMagnitude.magnitude amounts) b) :
    construct fq fr model upstream backend assetPoint base amounts b column = base column := by
  have absent := excluded
  simp only [ownedWrites,List.mem_append,List.mem_singleton,not_or] at absent
  unfold construct blindedAssignment unsignedAssignment
  rw [{F}.outside _ column absent.2.2.2.2,
    {HF}.outside_column _ b column absent.2.2.2.1,
    {V}.outside_column _ _ _ _ _ _ _ _ column absent.2.2.1,
    {S}.preserves _ amounts column absent.2.1,{L}.outside base column absent.1]
theorem outside_eval (amounts : TransferSignedMagnitude.Inputs) (b : Nat) (terms : Linear)
    (excluded : ∀ term ∈ terms, term.1 ∉ ownedWrites (TransferSignedMagnitude.magnitude amounts) b) :
    eval (construct fq fr model upstream backend assetPoint base amounts b) terms = eval base terms := by
  apply eval_agrees
  intro term member
  exact outside_column fq fr model upstream backend assetPoint base amounts b term.1 (excluded term member)
private theorem variable_shared (amounts : TransferSignedMagnitude.Inputs) (column : Nat)
    (included : column ∈ [0,2,9,{copy},{neg}]) :
    unsignedAssignment fq fr model upstream backend assetPoint base amounts column =
      {S}.completeAssignment ({L}.construct base) amounts column := by
  let n := TransferSignedMagnitude.magnitude amounts
  let signedBase := {S}.completeAssignment ({L}.construct base) amounts
  have selection : ([0,2,9,{copy},{neg}] : List Nat).all (fun column => decide
    (column ∈ {V}.kept ∧ column ∉ {T}.allWrites ∧ (column < {start} ∨ {start}+129 ≤ column))) = true := by decide
  have selected := of_decide_eq_true (List.all_eq_true.mp selection column included)
  have loop := GroupFixedCircuitCompletion.run_preserves
    ({V}.prepared fq fr model upstream backend assetPoint signedBase n) ({V}.programs n)
    {V}.kept ({V}.protection n) column selected.1
  have native := {T}.outside fq fr model upstream backend assetPoint (writeBits signedBase {start} (encodeBits 129 n))
    column selected.2.1
  exact loop.trans (native.trans (writeBits_preserves signedBase {start} (encodeBits 129 n) column
    (by simpa only [encodeBits_length] using selected.2.2)))
theorem constructs (amounts : TransferSignedMagnitude.Inputs) (b : Nat) (canonical : b < Scalar.order)
    (one : base 0 = 1) (linked : base {copy} = base 0) (blinding : base 2 = (b : Fld))
    (nativeAmounts : ∀ i, base ({S}.amountColumns i) = ((amounts i).val : Fld))
    (imaginary : Fld) (nonSquare : Group.NoUnitSquare ({D}.coefficientD : Fld))
    (imaginarySquare : imaginary*imaginary = -1) (four : (4 : Fld) ≠ 0)
    (valueBlinding : J) (valueBlindingRole : ({A}.generator : Group.Point Fld) = model.coordinates valueBlinding) :
    Satisfies (construct fq fr model upstream backend assetPoint base amounts b)
      (ownedRows (TransferSignedMagnitude.magnitude amounts)) ∧
    {F}.outputPoint (construct fq fr model upstream backend assetPoint base amounts b) =
      model.coordinates ((if TransferSignedMagnitude.negative amounts then
        -(TransferSignedMagnitude.magnitude amounts • upstream.embed (upstream.promote assetPoint)) else
          TransferSignedMagnitude.magnitude amounts • upstream.embed (upstream.promote assetPoint)) + b • valueBlinding) := by
  let n := TransferSignedMagnitude.magnitude amounts
  let unsigned := unsignedAssignment fq fr model upstream backend assetPoint base amounts
  let blinded := blindedAssignment fq fr model upstream backend assetPoint base amounts b
  have seededOne : {L}.construct base 0 = 1 := ({L}.outside base 0 (by decide)).trans one
  have seededLink : {L}.construct base {copy} = {L}.construct base 0 := by
    rw [{L}.outside base {copy} (by decide),{L}.outside base 0 (by decide),linked]
  have seededAmounts : ∀ i, {L}.construct base ({S}.amountColumns i) = ((amounts i).val : Fld) := by
    intro i
    have checked : ∀ i : Fin 4, {S}.amountColumns i ≠ 9 := by decide
    rw [{L}.outside base _ (checked i)]
    exact nativeAmounts i
  have variable := {V}.constructs_from_signed fq fr model upstream backend assetPoint ({L}.construct base) amounts
    seededOne seededLink seededAmounts imaginary nonSquare imaginarySquare
  have unsignedOne : unsigned 0 = 1 :=
    (variable_shared fq fr model upstream backend assetPoint base amounts 0 (by decide)).trans
      (({S}.preserves ({L}.construct base) amounts 0 (by decide)).trans seededOne)
  have unsignedLink : unsigned {copy} = unsigned 0 := by
    change unsignedAssignment fq fr model upstream backend assetPoint base amounts {copy} =
      unsignedAssignment fq fr model upstream backend assetPoint base amounts 0
    rw [variable_shared _ _ _ _ _ _ _ _ {copy} (by decide),variable_shared _ _ _ _ _ _ _ _ 0 (by decide),
      {S}.preserves ({L}.construct base) amounts {copy} (by decide),{S}.preserves ({L}.construct base) amounts 0 (by decide),seededLink]
  have scalar : eval unsigned {B}.privateValue = (b : Fld) := by
    have preserved := variable_shared fq fr model upstream backend assetPoint base amounts 9 (by decide)
    simpa only [{B}.privateValue,eval,Int.cast_one,one_mul,add_zero,{S}.preserves ({L}.construct base) amounts 9 (by decide),{L}.value,blinding] using preserved
  have builtH := {N}.actual_native_scalar_complete unsigned b canonical scalar unsignedOne four imaginary model
    nonSquare imaginarySquare valueBlinding valueBlindingRole unsignedLink
  have hOutside := GroupFrameExceptions.checked_rows 22738 {copy} hFrame hExceptions ({HF}.ownedWrites b)
    (signedVariableRows n) (h_writes_checked b) (h_rows_checked n)
  have retainedVariable : Satisfies blinded (signedVariableRows n) := by
    have shadow9 : unsigned 9 = base 2 :=
      (variable_shared fq fr model upstream backend assetPoint base amounts 9 (by decide)).trans
        (({S}.preserves ({L}.construct base) amounts 9 (by decide)).trans ({L}.value base))
    have target2 : unsigned 2 = base 2 :=
      (variable_shared fq fr model upstream backend assetPoint base amounts 2 (by decide)).trans
        (({S}.preserves ({L}.construct base) amounts 2 (by decide)).trans ({L}.outside base 2 (by decide)))
    have layoutRows : Satisfies unsigned {L}.rawRows := by
      intro row member
      have seedRow := {L}.constructs base row member
      have agrees (terms : Linear) (included : ∀ term ∈ terms, term ∈ row.a ++ row.b) :
          eval unsigned terms = eval ({L}.construct base) terms := by
        apply eval_agrees
        intro term present
        have bounded : {L}.rawRows.all (fun row => (row.a ++ row.b).all (fun term => decide (term.1 ∈ [2,9]))) = true := by decide
        have support := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp bounded row member) term (included term present))
        simp only [List.mem_cons,List.mem_singleton] at support
        rcases support with same | same
        · rw [same,target2,{L}.outside base 2 (by decide)]
        · rw [same,shadow9,{L}.value]
      change Square (eval unsigned row.a) (eval unsigned row.b)
      rw [agrees row.a (by intro term present; exact List.mem_append_left _ present),
        agrees row.b (by intro term present; exact List.mem_append_right _ present)]
      exact seedRow
    intro row member
    have agrees (terms : Linear) (included : ∀ term ∈ terms, term ∈ row.a ++ row.b) :
        eval blinded terms = eval unsigned terms := by
      apply {HF}.outside_eval
      intro term present
      exact hOutside row member term (included term present)
    change Square (eval blinded row.a) (eval blinded row.b)
    rw [agrees row.a (by intro term present; exact List.mem_append_left _ present),
      agrees row.b (by intro term present; exact List.mem_append_right _ present)]
    rcases List.mem_append.mp member with layoutMember | variableMember
    · exact layoutRows row layoutMember
    · exact variable.1 row variableMember
  have previous : Satisfies blinded (priorRows n) := by
    intro row member
    rcases List.mem_append.mp member with before | current
    · exact retainedVariable row before
    · exact builtH.1 row current
  have hShared : ([0,{copy},{neg}] : List Nat).all (fun column => decide (column ∉ {HF}.ownedWrites 0)) = true := by decide
  have hPreserves (column : Nat) (member : column ∈ [0,{copy},{neg}]) : blinded column = unsigned column :=
    {HF}.outside_column unsigned b column (by
      change column ∉ {HF}.ownedWrites 0
      exact of_decide_eq_true (List.all_eq_true.mp hShared column member))
  have blindedOne : blinded 0 = 1 := (hPreserves 0 (by decide)).trans unsignedOne
  have blindedLink : blinded {copy} = blinded 0 := by
    rw [hPreserves {copy} (by decide),hPreserves 0 (by decide),unsignedLink]
  have negative : eval blinded {F}.negative = if TransferSignedMagnitude.negative amounts then 1 else 0 := by
    simp only [{F}.negative,eval,Int.cast_one,one_mul,add_zero]
    rw [hPreserves {neg} (by decide),variable_shared fq fr model upstream backend assetPoint base amounts {neg} (by decide)]
    exact {S}.final_negative ({L}.construct base) amounts
  have unsignedEndpoint : {F}.unsignedPoint unsigned = model.coordinates (n • upstream.embed (upstream.promote assetPoint)) := by
    simpa only [{F}.unsignedPoint,{F}.unsignedX,{F}.unsignedY,{V}.programs,{V}.input,
      GroupFixedCircuitCompletion.output,GroupFixedCircuitCompletion.point,{','.join(p+'.program' for p in P)}] using variable.2
  have unsignedAbsent : ({F}.unsignedX ++ {F}.unsignedY).all (fun term => decide
    (term.1 ∉ {HF}.ownedWrites 0)) = true := by decide
  have unsignedPoint : {F}.unsignedPoint blinded = {F}.unsignedPoint unsigned := by
    change Group.Point.mk (eval blinded {F}.unsignedX) (eval blinded {F}.unsignedY) =
      Group.Point.mk (eval unsigned {F}.unsignedX) (eval unsigned {F}.unsignedY)
    apply congrArg₂ Group.Point.mk
    all_goals
      apply {HF}.outside_eval
      intro term present
      change term.1 ∉ {HF}.ownedWrites 0
      apply of_decide_eq_true
      apply List.all_eq_true.mp unsignedAbsent term
      first | exact List.mem_append_left _ present | exact List.mem_append_right _ present
  have blindingEndpoint : {F}.blindedPoint blinded = model.coordinates (b • valueBlinding) := by
    simpa only [{F}.blindedPoint,{F}.blindedX,{F}.blindedY,{A}.contribution,
      RuntimeBalanceBlindingChunk112.output,RuntimeBalanceBlindingWindow125.output,
      GroupFixedCircuitCompletion.point] using builtH.2
  have finalBuilt := {F}.actual_rows_complete blinded blindedOne blindedLink imaginary nonSquare imaginarySquare
    (TransferSignedMagnitude.negative amounts) negative
    (by rw [unsignedPoint,unsignedEndpoint]; exact model.onCurve _)
    (by rw [blindingEndpoint]; exact model.onCurve _)
  have finalOutside := GroupFrameExceptions.checked_rows 22738 {copy} finalFrame finalExceptions {F}.ownedWrites
    (priorRows n) final_writes_checked (final_rows_checked n)
  have keptRows := {F}.preserves_earlier_rows blinded (priorRows n) previous finalOutside
  refine ⟨?_,?_⟩
  · intro row member
    rcases List.mem_append.mp member with earlier | current
    · exact keptRows row earlier
    · exact finalBuilt.1 row current
  · have coordinates := finalBuilt.2
    rw [unsignedPoint,unsignedEndpoint,blindingEndpoint] at coordinates
    exact coordinates.trans (GroupSignedPoint.final_native ({D}.coefficientD : Fld) imaginary model
      nonSquare imaginarySquare (TransferSignedMagnitude.negative amounts)
      (n • upstream.embed (upstream.promote assetPoint)) (b • valueBlinding))
'''
    for export in ('h_writes_checked','h_rows_checked','final_writes_checked','final_rows_checked','outside_column','outside_eval','constructs'):
        source+='#print axioms '+export+'\n'
    return name,_signature_audits(source+f'end ShielddSecurity.{name}\n')
