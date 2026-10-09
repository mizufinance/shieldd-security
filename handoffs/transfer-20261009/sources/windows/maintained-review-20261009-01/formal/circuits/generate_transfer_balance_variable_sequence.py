"""Construct the actual balance65 row sequence after genuine five-page ingress.

The native point is a primitive SDK input interpreted by the existing reader.
The 129 bits are written from n, never supplied as a desired circuit fact.
Reuse of preceding signed/map assignments and the caller's native asset object
is a separate same-assignment join. No actual target is emitted before capture.
"""
from . import transfer_balance_variable_program as plans
from . import generate_transfer_balance_variable_completion as local
from . import transfer_relation as relation
from . import generate_transfer_signed_balance_completion as signed_renderer
from . import transfer_balance_input_layout as input_layout
import hashlib
import re
from .generate_hash_round import _signature_audits


def generate(parent,pages,digest,signed,asset_base,extracted,readonly_lcs=(),*,compiler_origin=22738):
    accepted=plans.plan(parent,pages,digest,signed,asset_base,extracted,readonly_lcs,
        compiler_origin=compiler_origin)
    kept=_kept(accepted,signed)
    result={}
    for item in accepted['programs']:
        ordinal=item['page_ordinal'];offset=item['window_offset']
        name,source=local.render_program(accepted['checked']['chunks'][ordinal],accepted['selections'][ordinal],
            offset,readonly_lcs,compiler_origin=compiler_origin,sequence_kept=kept)
        if name in result:raise relation.RelationError('balance65 duplicate actual local program')
        result[name]=source
    result.update(render_modules(accepted,kept,compiler_origin,signed))
    return result


def render_modules(accepted,kept,origin,signed=None):
    """Give the signed composition a fresh finite Lean module budget.

    Statements and constructors stay in the same namespace. The second
    module imports the first; it never reopens its implementations or treats
    a failed partial module as a qualified dependency.
    """
    name,source=_render(accepted,kept,origin,signed)
    if signed is None:
        return {name:source}
    source=re.sub(r'^set_option pp\.all true in\n#check @[A-Za-z0-9_]+\n#print axioms [A-Za-z0-9_]+\n',
                  '',source,flags=re.MULTILINE)
    marker='-- Exact maintained Signed constructor SHA256 '
    if source.count(marker)!=1:
        raise relation.RelationError('balance sequence exact signed theorem boundary')
    before,after=source.split(marker,1)
    end=f'end ShielddSecurity.{name}\n'
    if not after.endswith(end):
        raise relation.RelationError('balance sequence exact namespace closure')
    variables=before[before.index('variable {F : Type}'):before.index('def prepared (n : Nat)')]
    audits=lambda names:''.join('#print axioms '+n+'\n'for n in names)
    base_exports=['certified_bounds','protection','bit_value','constructs','scalar_endpoint','outside_column','outside_eval']
    core=_signature_audits(before+audits(base_exports)+end)
    extension=_signature_audits(f'import ShielddSecurity.{name}\nnamespace ShielddSecurity.{name}\n'
        'set_option maxHeartbeats 500000\nset_option maxRecDepth 4096\n'+variables+
        marker+after[:-len(end)]+audits(['reuse_signed_bits','constructs_from_signed'])+end)
    return {name:core,name+'Signed':extension}


def _signed_support(accepted,signed):
    first=accepted['checked']['chunks'][0]
    if (not input_layout.same_original_identity(signed.get('identity'),accepted['identity']) or signed.get('copy')!=first['metadata']['constant_copy'] or
            signed.get('metadata_sha256')!=first['signed_parent_metadata_sha256'] or
            signed.get('bits')!=[first['derived'][handle][0][0] for handle in first['bits']]):
        raise relation.RelationError('balance65 exact preceding signed135 source/row parent')
    # Reuse the maintained signed row renderer's semantic shape refusals.
    signed_renderer._from_checked(signed)
    if not isinstance(signed.get('raw_rows'),list) or len(signed['raw_rows'])!=135:
        raise relation.RelationError('balance65 exact preceding signed135 rows')
    support=set()
    for row in signed['raw_rows']:
        for side in ('a','b'):
            relation.terms(row[side],first['metadata']['domain_size'])
            support.update(c for c,_ in row[side])
    if support&set(accepted['writes']):
        raise relation.RelationError('balance65 table/window writes destroy preceding signed row support')
    return support


def _kept(accepted,signed=None):
    first=accepted['checked']['chunks'][0]
    columns=[first['derived'][handle] for handle in first['bits']]
    if (len(columns)!=129 or any(len(terms)!=1 or terms[0][1]!=1 for terms in columns) or
            [terms[0][0] for terms in columns]!=list(range(columns[0][0][0],columns[0][0][0]+129))):
        raise relation.RelationError('balance65 exact signed129 contiguous singleton bit inputs')
    if any(value[0]!='source' for key in ('base','twice','triple') for value in first['points'][key]):
        raise relation.RelationError('balance65 exact source native table coordinates required')
    table={c for key in ('base','twice','triple') for value in first['points'][key]
        for c,_ in first['derived'][value[1]]}
    signed_support=set() if signed is None else _signed_support(accepted,signed)
    kept=sorted(set(accepted['protected'])|table|signed_support)
    if any(set(item['writes'])&set(kept) for item in accepted['programs']):
        raise relation.RelationError('balance65 window overwrites signed bits/native shared table')
    return kept


def _render(accepted,kept,origin,signed=None):
    if len(accepted['programs'])!=65:
        raise relation.RelationError('balance65 whole renderer requires all actual windows')
    first=accepted['checked']['chunks'][0];copy=first['metadata']['constant_copy']
    start=first['derived'][first['bits'][0]][0][0]
    P=[local.PREFIX+f'{i:03d}Program' for i in range(65)]
    T=local.PREFIX+'000NativePrecompute';D=local.PREFIX+'000Point0Cones'
    A=local.PREFIX+'000Point1Completion';C=local.PREFIX+'000Point1Cones'
    name='RuntimeBalanceVariableSequence'
    bit=lambda i:f'(encodeBits 129 n)[{i}]?.getD false'
    pair=lambda i:(bit(128-2*i),'false' if i==0 else bit(129-2*i))
    program=lambda i:f'({P[i]}.program ({pair(i)[0]}) ({pair(i)[1]}))'
    programs='['+','.join(program(i) for i in range(65))+']'
    membership=' | '.join('rfl' for _ in range(65))
    arguments='fq fr model upstream backend point base'
    native='upstream.embed (upstream.promote point)'
    source=('import ShielddSecurity.RuntimeTransferSignedBalanceCompletion\n' if signed is not None else '')
    source+=''.join(f'import ShielddSecurity.{p}\n' for p in P)+f'''import ShielddSecurity.{T}
namespace ShielddSecurity.{name}
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
-- Actual qualified parent SHA256 {accepted['parent_sha256']}.
-- Exact ordinary relation SHA256 {accepted['identity']['relation_digest']}.
-- This owns native table/precompute and65 window rows, not earlier signed/map rows.
-- Same native asset object and idempotent reuse on the preceding constructed
-- assignment remain source/composition joins; seed columns are included in ownedWrites.
def kept : List Nat := {kept}
def programs (n : Nat) : List GroupFixedCircuitCompletion.Program := {programs}
def tables := {P[0]}.tables
def input : Linear × Linear := ([],[(0,1)])
def priorRows : List Row := {T}.firstRows ++ {C}.rawRows ++ {A}.quotientRaw
def ownedRows (n : Nat) : List Row := priorRows ++ GroupFixedCircuitCompletion.rows (programs n)
def ownedWrites (n : Nat) : List Nat := List.range' {start} 129 ++ {T}.allWrites ++
  (programs n).flatMap (fun program => program.stages.flatMap GroupCircuitCompletion.Step.writes)
def segments (n : Nat) : List (GroupFixedCircuitCompletion.Program × GroupFixedCircuitBounds.Frame) :=
  [{','.join(f'({program(i)},{P[i]}.afterFrame)' for i in range(65))}]
private theorem earlier_bounds (before localBefore after : GroupFixedCircuitBounds.Frame)
    (gap : before.low ≤ localBefore.low ∧ before.high ≤ localBefore.high)
    (program : GroupFixedCircuitCompletion.Program)
    (localBounds : (localBefore.low ≤ after.low ∧ localBefore.high ≤ after.high) ∧
      GroupFixedCircuitBounds.RowsCovered {origin} {copy} after program.rows ∧
      GroupFixedCircuitBounds.WritesOutside {origin} {copy} localBefore program) :
    (before.low ≤ after.low ∧ before.high ≤ after.high) ∧
      GroupFixedCircuitBounds.RowsCovered {origin} {copy} after program.rows ∧
      GroupFixedCircuitBounds.WritesOutside {origin} {copy} before program := by
  refine ⟨⟨Nat.le_trans gap.1 localBounds.1.1,Nat.le_trans gap.2 localBounds.1.2⟩,localBounds.2.1,?_⟩
  intro stage present column written covered
  apply localBounds.2.2 stage present column written
  rcases covered with low | high | copied
  · exact Or.inl (Nat.lt_of_lt_of_le low gap.1)
  · exact Or.inr (Or.inl ⟨high.1,Nat.lt_of_lt_of_le high.2 gap.2⟩)
  · exact Or.inr (Or.inr copied)
theorem certified_bounds (n : Nat) :
    GroupFixedCircuitBounds.Certified {origin} {copy} {P[0]}.beforeFrame (segments n) := by
  unfold segments
'''
    for i,p in enumerate(P):
        before=P[max(0,i-1)]+('.beforeFrame' if i==0 else '.afterFrame')
        source+=f'''  have current{i} := GroupFixedCircuitBounds.checked_local {origin} {copy}
    {p}.beforeFrame {p}.afterFrame {program(i)} ({p}.checked_bounds ({pair(i)[0]}) ({pair(i)[1]}))
  have bounded{i} := earlier_bounds {before} {p}.beforeFrame {p}.afterFrame (by decide) {program(i)} current{i}
  refine ⟨bounded{i}.1,bounded{i}.2.1,bounded{i}.2.2,?_⟩
'''
    source+=f'''  trivial
theorem protection (n : Nat) : ∀ program ∈ programs n, GroupFixedCircuitCompletion.Protected kept program := by
  intro program member
  simp only [programs,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with {membership}
'''
    for i,p in enumerate(P):source+=f'  · exact {p}.sequence_protected ({pair(i)[0]}) ({pair(i)[1]})\n'
    source+=f'''variable {{F : Type}} [Field F] [CharP F {local.PREFIX}000Point0Completion.modulus]
variable {{E S R K Q Signing J : Type}} [AddCommGroup J]
variable (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
variable (model : Group.StandardCurveModel J ({D}.coefficientD : F))
variable (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr ({D}.coefficientD : F) model)
variable {{Encoded Native : Type}} (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
variable (point : S) (base : Nat → F)
def prepared (n : Nat) : Nat → F := {T}.completed fq fr model upstream backend point
  (writeBits base {start} (encodeBits 129 n))
def construct (n : Nat) : Nat → F := GroupFixedCircuitCompletion.run (prepared {arguments} n) (programs n)
theorem bit_value (n index : Nat) (bound : index < 129) :
    prepared {arguments} n ({start}+index) = if (encodeBits 129 n)[index]?.getD false then 1 else 0 := by
  have absent : (List.range' {start} 129).all (fun column => decide (column ∉ {T}.allWrites)) = true := by decide
  unfold prepared
  rw [{T}.outside _ _ _ _ _ _ _ ({start}+index)
    (of_decide_eq_true (List.all_eq_true.mp absent _ (List.mem_range'_1.mpr (by omega))))]
  simp only [writeBits,encodeBits_length,Nat.add_sub_cancel_left,if_pos (show {start} ≤ {start}+index ∧
    {start}+index < {start}+129 by omega)]
theorem constructs (n : Nat) (one : base 0 = 1) (linked : base {copy} = base 0)
    (imaginary : F) (nonSquare : Group.NoUnitSquare ({D}.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    Satisfies (construct {arguments} n) (ownedRows n) ∧
      Group.OnCurve ({D}.coefficientD : F)
        (GroupFixedCircuitCompletion.point (construct {arguments} n)
          (GroupFixedCircuitCompletion.output input (programs n))) ∧
      GroupFixedCircuitCompletion.point (construct {arguments} n)
        (GroupFixedCircuitCompletion.output input (programs n)) =
          model.coordinates (binary (encodeBits 129 n) • ({native})) := by
  let written := writeBits base {start} (encodeBits 129 n)
  have writtenOne : written 0 = 1 := (writeBits_preserves base {start} (encodeBits 129 n) 0
    (by simp only [encodeBits_length]; omega)).trans one
  have writtenLink : written {copy} = written 0 := by
    dsimp only [written]
    rw [writeBits_preserves _ _ _ {copy} (by simp only [encodeBits_length]; decide),
      writeBits_preserves _ _ _ 0 (by simp only [encodeBits_length]; omega),linked]
  have initial := {T}.native_precompute_complete fq fr model upstream backend point written
    imaginary nonSquare imaginarySquare writtenOne writtenLink
  have nativeTables := {T}.native_table_coordinates fq fr model upstream backend point written
    imaginary nonSquare imaginarySquare writtenOne writtenLink
  let rho := prepared {arguments} n
  have rhoOne : rho 0 = 1 := ({T}.outside _ _ _ _ _ _ _ 0 (by decide)).trans writtenOne
  have rhoLink : rho {copy} = rho 0 := by
    change {T}.completed fq fr model upstream backend point written {copy} =
      {T}.completed fq fr model upstream backend point written 0
    rw [{T}.outside _ _ _ _ _ _ _ {copy} (by decide),{T}.outside _ _ _ _ _ _ _ 0 (by decide),writtenLink]
  have incoming : GroupFixedCircuitCompletion.point rho input = model.coordinates 0 := by
    rw [model.identity]
    simp only [input,GroupFixedCircuitCompletion.point,Group.identityPoint,eval,rhoOne,
      List.map_nil,List.sum_nil,List.map_cons,List.sum_cons,Int.cast_one,one_mul,add_zero]
  have nativeBase : GroupFixedCircuitCompletion.point rho tables.base = model.coordinates ({native}) := nativeTables.1
  have nativeTwice : GroupFixedCircuitCompletion.point rho tables.twice = model.coordinates (2 • ({native})) := nativeTables.2.1
  have nativeTriple : GroupFixedCircuitCompletion.point rho tables.triple = model.coordinates (3 • ({native})) := nativeTables.2.2
  have curved : GroupVariableCircuitCompletion.Curved ({D}.coefficientD : F) tables rho := by
    unfold GroupVariableCircuitCompletion.Curved
    rw [nativeBase,nativeTwice,nativeTriple]
    exact ⟨model.onCurve _,model.onCurve _,model.onCurve _⟩
  have localConstructors : ∀ program ∈ programs n,
    GroupVariableCircuitCompletion.LocalConstruct ({D}.coefficientD : F) {copy} tables program := by
    intro program member
    simp only [programs,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with {membership}
'''
    for i,p in enumerate(P):source+=f'    · exact {p}.local_constructor imaginary nonSquare imaginarySquare ({pair(i)[0]}) ({pair(i)[1]})\n'
    source+=f'''  have formulas : ∀ program ∈ programs n,
    GroupVariableCircuitNative.LocalFormula ({D}.coefficientD : F) {copy} tables program := by
    intro program member
    simp only [programs,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with {membership}
'''
    for i,p in enumerate(P):source+=f'    · exact {p}.local_formula imaginary nonSquare imaginarySquare ({pair(i)[0]}) ({pair(i)[1]})\n'
    source+=f'''  have tableSupports : ∀ term ∈ tables.terms, term.1 ∈ kept := by
    have checked : tables.terms.all (fun term => decide (term.1 ∈ kept)) = true := by decide
    intro term member
    exact of_decide_eq_true (List.all_eq_true.mp checked term member)
  have bitSupports : ∀ program ∈ programs n, ∀ term ∈ program.low ++ program.high, term.1 ∈ kept := by
    have checked : (programs 0).all (fun program => (program.low ++ program.high).all
      (fun term => decide (term.1 ∈ kept))) = true := by decide
    change (programs n).all (fun program => (program.low ++ program.high).all
      (fun term => decide (term.1 ∈ kept))) = true at checked
    intro program member term present
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked program member) term present)
  have initialCovered : GroupFixedCircuitBounds.RowsCovered {origin} {copy} {P[0]}.beforeFrame priorRows := by
    have checked : priorRows.all (fun row => (row.a ++ row.b).all
      (fun term => decide (GroupFixedCircuitBounds.covers {origin} {copy} {P[0]}.beforeFrame term.1))) = true := by decide
    intro row member term present
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked row member) term present)
  have fresh := GroupFixedCircuitBounds.bounded_fresh {origin} {copy} {P[0]}.beforeFrame
    priorRows (segments n) initialCovered (certified_bounds n)
  change GroupFixedCircuitCompletion.Fresh priorRows (programs n) at fresh
  have aligned : GroupFixedCircuitCompletion.Aligned input (programs n) := by
    simp only [programs,input,GroupFixedCircuitCompletion.Aligned,{','.join(p+'.program' for p in P)},and_self]
  have meanings : ∀ program ∈ programs n,
    eval rho program.low = (if program.lowBit then 1 else 0) ∧
    eval rho program.high = (if program.highBit then 1 else 0) := by
    intro program member
    simp only [programs,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with {membership}
'''
    for i,p in enumerate(P):
        # These source bits were checked as contiguous unit LCs by _kept.
        # State their actual terms, so the consumer also accepts qualified
        # renamed implementations that expose no per-window selector module.
        low_lc=f'[({start+128-2*i},1)]'
        high_lc='[]' if i==0 else f'[({start+129-2*i},1)]'
        source+=f'''    · change eval rho {low_lc} = _ ∧ eval rho {high_lc} = _
      simp only [eval,Int.cast_one,one_mul,add_zero,List.map_nil,List.sum_nil]
      exact ⟨bit_value {arguments} n {128-2*i} (by decide),'''
        source+=('by rfl⟩\n' if i==0 else f'bit_value {arguments} n {129-2*i} (by decide)⟩\n')
    source+=f'''  have built := GroupVariableCircuitCompletion.constructs ({D}.coefficientD : F) {copy}
    rho tables (programs n) input priorRows kept localConstructors (protection n) tableSupports bitSupports
    fresh aligned (by decide) (by decide) rhoOne rhoLink initial.1
    (by rw [incoming]; exact model.onCurve 0) curved meanings
  have pairOrder : GroupVariableCircuitNative.pairs (programs n) =
      (GroupNativeMultiply.pairBits (encodeBits 129 n)).reverse := by rfl
  have endpoint := GroupVariableCircuitNative.scalar_coordinates ({D}.coefficientD : F) {copy}
    model ({native}) rho tables (programs n) input kept (encodeBits 129 n) formulas (protection n)
    tableSupports bitSupports aligned (by decide) (by decide) rhoOne rhoLink incoming
    nativeBase nativeTwice nativeTriple meanings pairOrder
  exact ⟨built.1,built.2.1,endpoint⟩
theorem scalar_endpoint (n : Nat) (bounded : n < 2^129)
    (one : base 0 = 1) (linked : base {copy} = base 0)
    (imaginary : F) (nonSquare : Group.NoUnitSquare ({D}.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    GroupFixedCircuitCompletion.point (construct {arguments} n)
      (GroupFixedCircuitCompletion.output input (programs n)) = model.coordinates (n • ({native})) := by
  have endpoint := (constructs {arguments} n one linked imaginary nonSquare imaginarySquare).2.2
  rw [encodeBits_value 129 n bounded] at endpoint
  exact endpoint
theorem outside_column (n column : Nat) (excluded : column ∉ ownedWrites n) :
    construct {arguments} n column = base column := by
  have noBits : column ∉ List.range' {start} 129 := by
    intro member; exact excluded (List.mem_append_left _ (List.mem_append_left _ member))
  have noPrecompute : column ∉ {T}.allWrites := by
    intro member; exact excluded (List.mem_append_left _ (List.mem_append_right _ member))
  have stages : ∀ program ∈ programs n, GroupFixedCircuitCompletion.Protected [column] program := by
    intro program member stage present current single written
    have same : current = column := List.mem_singleton.mp single
    subst current
    exact excluded (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨program,member,List.mem_flatMap.mpr ⟨stage,present,written⟩⟩))
  have loop := GroupFixedCircuitCompletion.run_preserves (prepared {arguments} n) (programs n)
    [column] stages column (List.mem_singleton_self column)
  have precompute := {T}.outside fq fr model upstream backend point
    (writeBits base {start} (encodeBits 129 n)) column noPrecompute
  have rangeOutside : column < {start} ∨ {start}+129 ≤ column := by
    by_contra denied
    exact noBits (List.mem_range'_1.mpr (by omega))
  exact loop.trans (precompute.trans (writeBits_preserves base {start} (encodeBits 129 n) column
    (by simpa only [encodeBits_length] using rangeOutside)))
theorem outside_eval (n : Nat) (terms : Linear)
    (excluded : ∀ term ∈ terms, term.1 ∉ ownedWrites n) :
    eval (construct {arguments} n) terms = eval base terms := by
  apply eval_agrees
  intro term member
  exact outside_column {arguments} n term.1 (excluded term member)
'''
    exports=['certified_bounds','protection','bit_value','constructs','scalar_endpoint','outside_column','outside_eval']
    if signed is not None:
        S='RuntimeTransferSignedBalanceCompletion'
        _,body=signed_renderer._from_checked(signed)
        product,auxiliary=signed['product'],signed['auxiliary']
        source+=f'''-- Exact maintained Signed constructor SHA256 {hashlib.sha256(body.encode()).hexdigest()}.
theorem reuse_signed_bits [DecidableEq F] (amounts : TransferSignedMagnitude.Inputs) :
    writeBits ({S}.completeAssignment base amounts) {start}
      (encodeBits 129 (TransferSignedMagnitude.magnitude amounts)) = {S}.completeAssignment base amounts := by
  funext column
  by_cases inside : {start} ≤ column ∧ column < {start}+129
  · have noProduct : column ∉ [{product},{auxiliary}] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false]
      omega
    have ownBit : {S}.completeAssignment base amounts column =
        if (encodeBits 129 (TransferSignedMagnitude.magnitude amounts))[column-{start}]?.getD false then 1 else 0 := by
      unfold {S}.completeAssignment
      rw [ScalarCompletion.extend_product_preserves _ _ _ _ _ _ _ noProduct]
      simp only [{S}.bitAssignment,writeBits,encodeBits_length,if_pos inside]
    simp only [writeBits,encodeBits_length,if_pos inside,ownBit]
  · simp only [writeBits,encodeBits_length,if_neg inside]
theorem constructs_from_signed [DecidableEq F] (amounts : TransferSignedMagnitude.Inputs)
    (one : base 0 = 1) (linked : base {copy} = base 0)
    (nativeAmounts : ∀ i, base ({S}.amountColumns i) = ((amounts i).val : F))
    (imaginary : F) (nonSquare : Group.NoUnitSquare ({D}.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    let n := TransferSignedMagnitude.magnitude amounts
    let signedBase := {S}.completeAssignment base amounts
    Satisfies (construct fq fr model upstream backend point signedBase n) ({S}.rawRows ++ ownedRows n) ∧
      GroupFixedCircuitCompletion.point (construct fq fr model upstream backend point signedBase n)
        (GroupFixedCircuitCompletion.output input (programs n)) = model.coordinates (n • ({native})) := by
  dsimp only
  let n := TransferSignedMagnitude.magnitude amounts
  let signedBase := {S}.completeAssignment base amounts
  have signed := {S}.original_rows_complete base amounts one linked nativeAmounts
  have signedOne : signedBase 0 = 1 := ({S}.preserves base amounts 0 (by decide)).trans one
  have signedLink : signedBase {copy} = signedBase 0 := by
    change {S}.completeAssignment base amounts {copy} = {S}.completeAssignment base amounts 0
    rw [{S}.preserves base amounts {copy} (by decide),{S}.preserves base amounts 0 (by decide),linked]
  have built := constructs fq fr model upstream backend point signedBase n signedOne signedLink
    imaginary nonSquare imaginarySquare
  have precomputeOutside : {S}.rawRows.all (fun row => (row.a ++ row.b).all
    (fun term => decide (term.1 ∉ {T}.allWrites))) = true := by decide
  have supported : {S}.rawRows.all (fun row => (row.a ++ row.b).all
    (fun term => decide (term.1 ∈ kept))) = true := by decide
  have preparedSigned : Satisfies (prepared fq fr model upstream backend point signedBase n) {S}.rawRows := by
    change Satisfies ({T}.completed fq fr model upstream backend point
      (writeBits ({S}.completeAssignment base amounts) {start}
        (encodeBits 129 (TransferSignedMagnitude.magnitude amounts)))) {S}.rawRows
    rw [reuse_signed_bits base amounts]
    intro row member
    have agrees (terms : Linear) (included : ∀ term ∈ terms, term ∈ row.a ++ row.b) :
      eval ({T}.completed fq fr model upstream backend point signedBase) terms = eval signedBase terms := by
      apply eval_agrees
      intro term present
      exact {T}.outside _ _ _ _ _ _ _ term.1 (of_decide_eq_true
        (List.all_eq_true.mp (List.all_eq_true.mp precomputeOutside row member) term (included term present)))
    change Square (eval _ row.a) (eval _ row.b)
    rw [agrees row.a (by intro term present; exact List.mem_append_left _ present),
      agrees row.b (by intro term present; exact List.mem_append_right _ present)]
    exact signed row member
  have retained : Satisfies (construct fq fr model upstream backend point signedBase n) {S}.rawRows := by
    intro row member
    have agrees (terms : Linear) (included : ∀ term ∈ terms, term ∈ row.a ++ row.b) :
      eval (construct fq fr model upstream backend point signedBase n) terms =
        eval (prepared fq fr model upstream backend point signedBase n) terms := by
      apply eval_agrees
      intro term present
      exact GroupFixedCircuitCompletion.run_preserves (prepared fq fr model upstream backend point signedBase n)
        (programs n) kept (protection n) term.1 (of_decide_eq_true
          (List.all_eq_true.mp (List.all_eq_true.mp supported row member) term (included term present)))
    change Square (eval _ row.a) (eval _ row.b)
    rw [agrees row.a (by intro term present; exact List.mem_append_left _ present),
      agrees row.b (by intro term present; exact List.mem_append_right _ present)]
    exact preparedSigned row member
  refine ⟨?_,scalar_endpoint fq fr model upstream backend point signedBase n
    (TransferSignedMagnitude.magnitude_bound amounts) signedOne signedLink imaginary nonSquare imaginarySquare⟩
  intro row member
  rcases List.mem_append.mp member with previous | current
  · exact retained row previous
  · exact built.1 row current
'''
        exports+=['reuse_signed_bits','constructs_from_signed']
    for export in exports:
        source+='#print axioms '+export+'\n'
    return name,_signature_audits(source+f'end ShielddSecurity.{name}\n')
