"""Owned IVK/precompute/all126 row constructor, independently of output meaning.

Global SDK/codec/standard-curve contracts remain explicit. The returned SDK Fr
integer supplies the actual written bit fields; actual native precomputation
supplies all table/input/row invariants. No previous row truth or desired point
is a premise. Prefix row preservation and native scalar endpoint are separate.
"""
from . import generate_transfer_ownership_constructor_trace as trace
from . import generate_transfer_ownership_constructor_bits as bit_adapters
from . import generate_transfer_ownership_precompute_tables as tables
from . import generate_transfer_ivk_native_bit_values as bit_values
from . import generate_transfer_ivk_reduction_join as joins


def _bit_columns(start):
    """Private finite certificates, at most16 physical columns per check."""
    result=''
    for offset in range(0,252,16):
        width=min(16,252-offset)
        result+=f'''private theorem bit_columns{offset} : ∀ index < {width},
    {start+offset}+index ∈ T.sourceColumns := by
  have checked : (List.range' {start+offset} {width}).all
      (fun column => decide (column ∈ T.sourceColumns)) = true := by decide
  intro index bound
  have member : {start+offset}+index ∈ List.range' {start+offset} {width} := by
    exact List.mem_range'.mpr ⟨index,bound,by simp only [Nat.one_mul]⟩
  exact of_decide_eq_true (List.all_eq_true.mp checked _ member)
'''
    result+=f'''private theorem bit_columns : ∀ index < 252,
    {start}+index ∈ T.sourceColumns := by
  intro index bound
'''
    for offset in range(0,252,16):
        width=min(16,252-offset)
        if offset+width<252:
            result+=f'  by_cases below{offset} : index < {offset+width}\n'
            indent='  · '
        else:
            indent='  '
        if offset==0:
            result+=indent+'exact bit_columns0 index below0\n'
        else:
            result+=indent+f'have position : {start}+index = {start+offset}+(index-{offset}) := by omega\n'
            result+=('    ' if offset+width<252 else '  ')+'rw [position]\n'
            result+=('    ' if offset+width<252 else '  ')+f'exact bit_columns{offset} (index-{offset}) (by omega)\n'
    return result


def _constants(qs,rs,qcol,rcol,copy):
    """Opaque small bridges avoid defeq evaluation of the full506-stage run."""
    source=f'''private theorem seed_constants {{F : Type}} [Field F] {{Q Encoded Native : Type}}
    (fq : GroupNativeSdk.FqBytes Q) (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (nk x y : Q) (base : Nat → F) (column : Nat) (member : column ∈ [0,{copy}]) :
    S.seed fq backend nk x y base column = base column := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
'''
    for column in (0,copy):
        source+=f'  · exact S.seed_preserves fq backend nk x y base {column} (by decide)\n'
    source+=f'''private theorem hash_constants {{F : Type}} [Field F] (base : Nat → F)
    (column : Nat) (member : column ∈ [0,{copy}]) : H.completeAssignment base column = base column := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
'''
    for column in (0,copy):
        source+=f'  · exact H.preserves base {column} (by decide)\n'
    source+=f'''private theorem order_constants {{F : Type}} [Field F]
    (codec : TransferReduction.CanonicalField F) (base : Nat → F)
    (column : Nat) (member : column ∈ [0,{copy}]) : O.construct codec base column = base column := by
  unfold O.construct
  apply ScalarReductionSupport.kept_column base codec (eval base O.hashValue)
    {qcol} {rcol} {qs} {rs} O.allStages O.kept O.ordered column
  all_goals
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> decide
private theorem hash_reduction_constants {{F : Type}} [Field F]
    (codec : TransferReduction.CanonicalField F) (base : Nat → F)
    (column : Nat) (member : column ∈ [0,{copy}]) :
    RuntimeTransferIvkHashReductionJoin.completed codec base column = base column := by
  unfold RuntimeTransferIvkHashReductionJoin.completed
  exact (order_constants codec (H.completeAssignment base) column member).trans
    (hash_constants base column member)
private theorem inverse_prefix_constants {{F : Type}} [Field F]
    (codec : TransferReduction.CanonicalField F) (base : Nat → F)
    (column : Nat) (member : column ∈ [0,{copy}]) :
    RuntimeTransferIvkInversePrefixJoin.completed codec base column = base column := by
  have outside : column ∉ I.ownedWrites := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> decide
  unfold RuntimeTransferIvkInversePrefixJoin.completed
  exact (I.preserves (RuntimeTransferIvkHashReductionJoin.completed codec base) column outside).trans
    (hash_reduction_constants codec base column member)
theorem ivk_constants {{F : Type}} [Field F] {{Q Encoded Native : Type}}
    (fq : GroupNativeSdk.FqBytes Q) (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (codec : TransferReduction.CanonicalField F) (nk x y : Q) (base : Nat → F) :
    ∀ column ∈ [0,{copy}], IV.completeAssignment fq backend codec nk x y base column = base column := by
  intro column member
  unfold IV.completeAssignment
  exact (inverse_prefix_constants codec (S.seed fq backend nk x y base) column member).trans
    (seed_constants fq backend nk x y base column member)
'''
    return source


def generate(chunks,selections,ivk_data,ivk_export,reduction_data,reduction_export,
             parameter_root,expected_relation,readonly_lcs=()):
    trace.generate(chunks,selections,readonly_lcs)
    tables.generate(chunks[0],selections[0],readonly_lcs)
    bit_values.generate(ivk_data,ivk_export,reduction_data,reduction_export,
                        parameter_root,expected_relation,readonly_lcs)
    native=bit_values.bits.consumer.keys.native
    accepted=native.hashes.ivk.inspect_metadata(ivk_data,parameter_root,expected_relation)
    plan=native.reduction.plan(reduction_data,accepted,reduction_export,expected_relation,readonly_lcs)
    q,r=plan['phases'][:2];qs,rs=q['start'],r['start'];qcol,rcol=q['value'][0][0],r['value'][0][0]
    copy=plan['checked']['metadata']['constant_copy']
    expected_bits=[((rs+index,1),) for index in range(252)]
    if r['width']!=252 or rs+252>2257 or any(
        checked['metadata']['relation_digest']!=expected_relation or checked['metadata']['constant_copy']!=copy or
        [checked['derived'][handle] for handle in checked['bits']]!=expected_bits for checked in chunks):
        raise native.reduction.relation.RelationError('ownership constructor exact accepted IVK physical-bit/relation join')
    for checked,selected in zip(chunks,selections):bit_adapters.generate(checked,selected,readonly_lcs)
    return _render(qs,rs,qcol,rcol,copy)


def _render(qs,rs,qcol,rcol,copy):
    """Pure proof template, only after the typed generate ingress checks above.

    Proof-only successors may use this with exact immutable typed-parent
    metadata and a strict allowed proof-delta check; it is not an ingress API.
    """
    if any(type(value) is not int or value<0 for value in (qs,rs,qcol,rcol,copy)):
        raise joins.reduction.relation.RelationError('native constructor natural template columns')
    if qs+4!=rs or qcol+1!=rcol or rcol+1!=qs or copy<=rs+252:
        raise joins.reduction.relation.RelationError('native constructor accepted reduction shape')
    name='RuntimeOwnershipNativeConstructor'
    aliases=dict(G='RuntimeOwnershipConstructorTrace',T='RuntimeOwnershipWindow000NativeTables',
        N='RuntimeOwnershipWindow000NativePrecompute',V='RuntimeTransferIvkNativeBitValuesOwned',
        IV='RuntimeTransferIvkNativeInverseOwned',S='ShielddViewingKeySeed',
        H='RuntimeTransferIvkHashOwnedCompletion',I='RuntimeTransferIvkInverseOwnedCompletion',
        O=joins.ORDER,D='RuntimeHashBlock_authorization_ivk_0',Z='RuntimeOwnershipConstructorChunk000')
    source=''.join(f'import ShielddSecurity.{module}\n' for module in (aliases['G'],aliases['T'],aliases['V']))
    source+=''.join(f'import ShielddSecurity.RuntimeOwnershipConstructorBits{start:03d}\n' for start in range(0,126,16))
    source+='''set_option maxHeartbeats 400000
set_option maxRecDepth 4096
'''+f'namespace ShielddSecurity.{name}\n'
    source+=''.join(f'namespace {key} := {value}\n' for key,value in aliases.items())
    source+=f'''open GroupFixedCircuitCompletion
def nativeBits {{R : Type}} (fr : GroupNativeSdk.FrBytes R) (scalar : R) : Nat → Bool :=
  fun index => (encodeBits 252 (fr.integer scalar))[index]?.getD false
'''
    source+=_constants(qs,rs,qcol,rcol,copy)
    source+=_bit_columns(rs)
    source+=f'''variable {{F : Type}} [Field F] [CharP F Scalar.modulus]
variable {{E S R K Q Signing J Encoded Native : Type}} [AddCommGroup J]
variable (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
variable (model : Group.StandardCurveModel J (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
variable (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr
  (RuntimeOwnershipWindow000Point0Cones.coefficientD : F) model)
variable (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
variable (codec : TransferReduction.CanonicalField F) (nk x y : Q) (sender : S) (scalar : R) (base : Nat → F)
def precomputed : Nat → F := N.completed fq fr model upstream backend sender
  (IV.completeAssignment fq backend codec nk x y base)
def completed : Nat → F := run (precomputed fq fr model upstream backend codec nk x y sender base)
  (G.programs (nativeBits fr scalar))
variable (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
variable (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
variable (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
variable (primitives : ShielddViewingKeyAdmission.Primitives fq fr)
variable (one : base 0 = 1) (linked : base {copy} = base 0)
variable (accepted : ShielddViewingKeyAdmission.incomingScalar primitives
  (ShielddNativeIvkSdkProgram.ivk fq arithmetic initial square codec
    (Poseidon.castParameters D.parameters) nk x y) = some scalar)
include one linked in
private theorem precomputed_constants :
    precomputed fq fr model upstream backend codec nk x y sender base 0 = 1 ∧
    precomputed fq fr model upstream backend codec nk x y sender base {copy} =
      precomputed fq fr model upstream backend codec nk x y sender base 0 := by
  let ivk := IV.completeAssignment fq backend codec nk x y base
  have ivkOne : ivk 0 = 1 := (ivk_constants fq backend codec nk x y base 0 (by simp)).trans one
  have ivkLink : ivk {copy} = ivk 0 := by
    dsimp only [ivk]
    rw [ivk_constants fq backend codec nk x y base {copy} (by simp),
      ivk_constants fq backend codec nk x y base 0 (by simp),linked]
  have oneBuilt := T.protected_columns fq fr model upstream backend sender ivk ivkLink 0 (by decide)
  have copyBuilt := T.protected_columns fq fr model upstream backend sender ivk ivkLink {copy} (by decide)
  exact ⟨oneBuilt.trans ivkOne,copyBuilt.trans (ivkLink.trans oneBuilt.symm)⟩
include arithmetic initial square primitives one linked accepted in
private theorem precomputed_values : ∀ index < 252,
    precomputed fq fr model upstream backend codec nk x y sender base ({rs}+index) =
      (if nativeBits fr scalar index then 1 else 0) := by
  let ivk := IV.completeAssignment fq backend codec nk x y base
  have ivkLink : ivk {copy} = ivk 0 := by
    dsimp only [ivk]
    rw [ivk_constants fq backend codec nk x y base {copy} (by simp),
      ivk_constants fq backend codec nk x y base 0 (by simp),linked]
  intro index bound
  exact (T.protected_columns fq fr model upstream backend sender ivk ivkLink _ (bit_columns index bound)).trans
    (V.native_values fq fr arithmetic initial square primitives backend codec nk x y scalar base one linked accepted index bound)
include arithmetic initial square primitives one linked accepted in
theorem native_windows_complete (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    Satisfies (completed fq fr model upstream backend codec nk x y sender scalar base) G.originalRows ∧
      Group.OnCurve (Z.coefficientD : F)
        (point (completed fq fr model upstream backend codec nk x y sender scalar base)
          (output G.input (G.programs (nativeBits fr scalar)))) ∧
      GroupVariableCircuitCompletion.Curved (Z.coefficientD : F) G.tables
        (completed fq fr model upstream backend codec nk x y sender scalar base) ∧
      (∀ column ∈ G.kept, completed fq fr model upstream backend codec nk x y sender scalar base column =
        precomputed fq fr model upstream backend codec nk x y sender base column) := by
  let ivk := IV.completeAssignment fq backend codec nk x y base
  let built := precomputed fq fr model upstream backend codec nk x y sender base
  have ivkOne : ivk 0 = 1 := (ivk_constants fq backend codec nk x y base 0 (by simp)).trans one
  have ivkLink : ivk {copy} = ivk 0 := by
    dsimp only [ivk]
    rw [ivk_constants fq backend codec nk x y base {copy} (by simp),
      ivk_constants fq backend codec nk x y base 0 (by simp),linked]
  have constants := precomputed_constants fq fr model upstream backend codec nk x y sender base one linked
  have written := precomputed_values fq fr model upstream backend codec nk x y sender scalar base
    arithmetic initial square primitives one linked accepted
  have values : ∀ program ∈ G.programs (nativeBits fr scalar),
      eval built program.low = (if program.lowBit then 1 else 0) ∧
      eval built program.high = (if program.highBit then 1 else 0) := by
    intro program member
    simp only [G.programs,List.mem_append] at member
    rcases member with '''+' | '.join('present' for _ in range(8))+'\n'
    source+=''.join(f'    · exact RuntimeOwnershipConstructorBits{start:03d}.field_values built (nativeBits fr scalar) written program present\n' for start in range(0,126,16))
    source+=f'''  exact G.constructs_from_precompute imaginary nonSquare imaginarySquare (nativeBits fr scalar) built constants.1 constants.2
    (T.prior_rows_complete fq fr model upstream backend sender ivk imaginary nonSquare imaginarySquare ivkOne ivkLink)
    (T.identity_input fq fr model upstream backend sender ivk ivkLink ivkOne)
    (T.table_curves fq fr model upstream backend sender ivk imaginary nonSquare imaginarySquare ivkOne ivkLink) values
include arithmetic initial square primitives one linked accepted in
theorem native_bit_values : ∀ index < 252,
    completed fq fr model upstream backend codec nk x y sender scalar base ({rs}+index) =
      (if nativeBits fr scalar index then 1 else 0) := by
  intro index bound
  have kept : {rs}+index ∈ G.kept := by
    apply List.mem_append_left
    apply List.mem_range.mpr
    omega
  exact (run_preserves _ (G.programs (nativeBits fr scalar)) G.kept (G.protected_programs _)
    _ kept).trans (precomputed_values fq fr model upstream backend codec nk x y sender scalar base
      arithmetic initial square primitives one linked accepted index bound)
'''
    for export in ('ivk_constants','native_windows_complete','native_bit_values'):
        source+='#print axioms '+export+'\n'
    return name,joins._qualify(source+f'end ShielddSecurity.{name}\n',aliases)
