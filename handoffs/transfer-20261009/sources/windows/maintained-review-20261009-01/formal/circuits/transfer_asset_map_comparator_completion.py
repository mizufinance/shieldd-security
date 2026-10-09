"""Canonical255 comparator construction from exact written bit meanings.

The integer is the canonical codec value, below the actual field modulus.
There is deliberately no 2^255<modulus assertion: direct bit-write decoding,
not modular reconstruction uniqueness, supplies the integer comparator input.
The source plan partitions at most eight actual source steps per chunk for
ScalarConstructedBits and the existing bounded compiler construction helpers.
"""
from . import transfer_asset_map as maps, transfer_asset_map_completion as completion
from . import transfer_arithmetic as arithmetic, transfer_relation as relation
from .transfer_balance_rows import canonical, combine


def plan(data, extracted, accepted_roles):
    whole = completion.plan(data, extracted, accepted_roles)
    checked = whole['checked'];comparisons = checked['comparisons'];rows = whole['normalized'];raw = whole['raw']
    copy = checked['metadata']['constant_copy'];bits = [whole['seeds']['bit' + str(i)] for i in range(255)]
    value = whole['seeds']['selectedRoot'];start = bits[0]
    if bits != list(range(start, start + 255)) or start <= value < start + 255:
        raise relation.RelationError('map comparator fresh contiguous255 original bit block')
    if len(comparisons) != 255:
        raise relation.RelationError('map comparator exact255 source recurrence')
    material_by_rows = {tuple(step['rows']): step for step in whole['steps']}
    chunks = [];previous_support = {0, value, *bits};all_material = [];indices = set();boundaries = {}
    for begin in range(0, 255, 8):
        fragment = comparisons[begin:begin + 8];steps = [];fragment_rows = set()
        for before, bit, factor, output, after, flag in fragment:
            cert = arithmetic.product_certificate(before, factor, output, rows)
            if cert['kind'] in ('folded_left', 'folded_right'):
                if cert['rows']:
                    raise relation.RelationError('map comparator folded product unexpectedly owns rows')
            else:
                step = material_by_rows.get(tuple(cert['rows']))
                if step is None or step['kind'] != 'product':
                    raise relation.RelationError('map comparator exact fresh product construction required')
                if cert.get('swapped'):
                    # CompilerCompletion handles its exact captured factors;
                    # the source recurrence certificate separately records order.
                    if (step['left'], step['right']) != (factor, before):
                        raise relation.RelationError('map comparator swapped source factor mismatch')
                elif (step['left'], step['right']) != (before, factor):
                    raise relation.RelationError('map comparator original source factor mismatch')
                steps.append(step);fragment_rows.update(step['rows'])
            boolean = [i for i, row in rows.items() if row == (bit, bit)]
            if len(boolean) != 1:
                raise relation.RelationError('map comparator exact original Boolean row')
            fragment_rows.add(boolean[0])
        if not steps:
            raise relation.RelationError('map comparator empty construction chunk')
        floor = min(c for step in steps for c in step['writes'])
        upper = max(c for step in steps for c in step['writes']) + 1
        if any(c >= floor for c in previous_support):
            raise relation.RelationError('map comparator previous rows exceed exact numeric allocation fence')
        cursor = floor
        for step in steps:
            if not (cursor <= step['output'] < step['auxiliary']) or any(
                    c >= step['output'] for lc in (step['left'], step['right'], step['remainder']) for c, _ in lc):
                raise relation.RelationError('map comparator unsupported original allocation order')
            cursor = step['auxiliary'] + 1
            previous_support.update(c for lc in (step['left'], step['right'], step['remainder']) for c, _ in lc)
            previous_support.update(step['writes'])
        if cursor != upper:
            raise relation.RelationError('map comparator exact chunk upper cursor')
        all_material.extend(steps);indices.update(fragment_rows)
        chunks.append(dict(start=begin, comparisons=fragment, steps=steps,
                           floor=floor, upper=upper, rows=sorted(fragment_rows)))
    weighted = canonical((column, 2**i) for i, column in enumerate(bits))
    for label, a, b in (('reconstruction', weighted, ((value, 1),)),
                         ('endpoint', checked['canonical'][1], maps.ONE)):
        delta = combine(a, b, -1)
        matched = [i for i, row in rows.items() if row in ((delta, ()), (maps._scale(delta, -1), ()))]
        if len(matched) != 1:
            raise relation.RelationError('map comparator exact original ' + label)
        indices.add(matched[0])
        boundaries[label] = matched[0]
    links = [i for i, row in raw.items() if row == (canonical([(0, 1), (copy, -1)]), ())]
    if len(links) != 1:
        raise relation.RelationError('map comparator exact kept constant link')
    indices.update(links)
    boundaries['link'] = links[0]
    boolean_indices = []
    for column in bits:
        matches = [i for i, row in raw.items() if row == (((column, 1),), ((column, 1),))]
        if len(matches) != 1:
            raise relation.RelationError('map comparator exact original singleton Boolean row')
        boolean_indices.append(matches[0])
    partition = boolean_indices + [i for chunk in chunks for step in chunk['steps'] for i in step['rows']] + list(boundaries.values())
    if len(partition) != len(set(partition)) or set(partition) != indices:
        raise relation.RelationError('map comparator original row ownership partition')
    # Independently check the exact boundary templates emitted below. A
    # failing Lean decide is never accepted as row correspondence evidence.
    expected_boundaries = [
        (combine(weighted, ((value, 1),), -1), ()),
        (combine(checked['canonical'][1], maps.ONE, -1), ()),
        ((), ())]
    for label, expected in zip(('reconstruction', 'endpoint', 'link'), expected_boundaries):
        actual = rows[boundaries[label]]
        if actual not in (expected, (maps._scale(expected[0], -1), expected[1])):
            raise relation.RelationError('map comparator original signed boundary template ' + label)
    owned = sorted({value, *bits, *(c for step in all_material for c in step['writes'])})
    return dict(checked=checked, bits=bits, value=value, steps=all_material, chunks=chunks,
                owned_writes=owned, raw={i: raw[i] for i in sorted(indices)},
                boundaries=boundaries, boolean_indices=boolean_indices, original_partition=partition)


def construct(data, extracted, accepted_roles, base, canonical_value):
    """Executable exact row test; no Lean/kernel/qualification claim."""
    recipe = plan(data, extracted, accepted_roles)
    if type(canonical_value) is not int or not 0 <= canonical_value < maps.P:
        raise relation.RelationError('map comparator value must be canonical field integer')
    copy = recipe['checked']['metadata']['constant_copy'];rho = dict(base)
    if rho.get(0) != 1 or rho.get(copy) != 1:
        raise relation.RelationError('map comparator kept constant link must be one')
    rho[recipe['value']] = canonical_value
    for i, column in enumerate(recipe['bits']):
        rho[column] = canonical_value >> i & 1
    evaluate = lambda lc: sum(rho.get(c, 0) * n for c, n in lc) % maps.P
    for step in recipe['steps']:
        left, right = evaluate(step['left']), evaluate(step['right'])
        rho[step['output']] = (left * right - evaluate(step['remainder'])) % maps.P
        rho[step['auxiliary']] = (left - right)**2 % maps.P
    if any(evaluate(a)**2 % maps.P != evaluate(b) for a, b in recipe['raw'].values()):
        raise relation.RelationError('map comparator original constructed row failed')
    if any(rho.get(c, 0) != v for c, v in base.items() if c not in recipe['owned_writes']):
        raise relation.RelationError('map comparator outside ownership changed')
    return dict(assignment=rho, plan=recipe, proof=False,
                scope='executable original255 comparison/endpoint/reconstruction rows only; kernel qualification remains separate')


def generate_chunks(data, extracted, accepted_roles):
    """Bounded actual product constructors and exact source-step certificates.

    Each chunk's order extends an arbitrary preceding row list from a symbolic
    support bound. Its arithmetic constructor completes only its product rows;
    the independent Boolean/source-chain certificates are data for the full
    written-bit composition, not an assumed comparison result.
    """
    from .generate_hash_round import linear, signed, _signature_audits
    recipe = plan(data, extracted, accepted_roles)
    normalized = completion.plan(data, extracted, accepted_roles)['normalized']
    checked = recipe['checked'];copy = checked['metadata']['constant_copy'];modules = {}
    for number, chunk in enumerate(recipe['chunks']):
        name = 'RuntimeTransferAssetMapComparatorConstruction' + str(number)
        steps = chunk['steps'];indices = sorted({i for step in steps for i in step['rows']})
        records = []
        for before, bit, factor, product, after, flag in chunk['comparisons']:
            cert = arithmetic.product_certificate(before, factor, product, normalized)
            if cert.get('swapped'):
                raise relation.RelationError('map comparator source-chain swapped orientation not yet transported')
            kind = cert['kind']
            if kind == 'product':
                datum = '.product ' + linear(cert['auxiliary'])
            elif kind == 'square':
                datum = '.square'
            else:
                datum = ('.foldedLeft ' if kind == 'folded_left' else '.foldedRight ') + f'({signed(cert["coefficient"])} : Int)'
            records.append('{ before := ' + linear(before) + ', left := ' + linear(bit) +
                           ', after := ' + linear(after) + ', right := ' + ('true' if flag else 'false') +
                           ', factor := ' + linear(factor) + ', target := ' + linear(product) +
                           ', product := ' + datum + ' }')
        source = f'''import ShielddSecurity.ScalarRandomizerBounds
import ShielddSecurity.CompilerSignedCompletion
import ShielddSecurity.PoseidonCompletion
set_option maxHeartbeats 300000
set_option maxRecDepth 2048
namespace ShielddSecurity.{name}
-- Exact metadata SHA256 {checked['metadata_sha256']}.
-- Only owned numeric products; full canonical255 endpoint is composed separately.
def modulus : Nat := {maps.P}
def kept : List Nat := [0,1,2,{copy},{recipe['value']}] ++ List.range' {recipe['bits'][0]} 255
def lower : Nat := {chunk['floor']}
def upper : Nat := {chunk['upper']}
def originalRows : List Nat := {indices}
def rawRows : List Row := [
''' + ',\n'.join('⟨' + linear(recipe['raw'][i][0]) + ',' + linear(recipe['raw'][i][1]) + '⟩'
                 for i in indices) + ''']
def steps : List CompilerCompletion.Step := [
''' + ',\n'.join('.product ' + linear(s['left']) + ' ' + linear(s['right']) + ' ' + linear(s['remainder']) +
                 ' ' + str(s['output']) + ' ' + str(s['auxiliary']) for s in steps) + ''']
def sourceSteps : List ScalarRows.StepData := [
''' + ',\n'.join(records) + f''']
def initial : Linear := {linear(chunk['comparisons'][0][0])}
def endpoint : Linear := {linear(chunk['comparisons'][-1][4])}
def expectedLocalRows : List Row :=
  (List.range' {recipe['bits'][0] + chunk['start']} {len(chunk['comparisons'])}).map booleanRow ++
  CompilerCompletion.emitted steps
def completeAssignment {{F : Type}} [Field F] (rho : Nat → F) : Nat → F :=
  CompilerCompletion.run rho steps

theorem bounded_checked : ScalarRandomizerBounds.checkBounded lower upper steps = true := by decide
theorem protected_checked : ScalarRandomizerBounds.checkProtected kept steps = true := by decide
theorem rows_below : ScalarRandomizerBounds.RowsBelow upper (CompilerCompletion.emitted steps) :=
  ScalarRandomizerBounds.bounded_rows lower upper steps bounded_checked
theorem ordered (prior : List Row) (below : ScalarRandomizerBounds.RowsBelow lower prior) :
    CompilerCompletion.Topological kept prior steps :=
  ScalarRandomizerBounds.bounded_ordered lower upper steps kept prior bounded_checked below
    (ScalarRandomizerBounds.protected_certificate kept steps protected_checked)

theorem source_chain_checked : ScalarRows.checkChain modulus expectedLocalRows initial sourceSteps = true := by decide
theorem source_bits_checked : ScalarBits.checkBits modulus expectedLocalRows
    (sourceSteps.map ScalarRows.StepData.left) = true := by decide
theorem endpoint_checked : ScalarComparisonBounds.endpoint initial sourceSteps = endpoint := by rfl

theorem coverage_checked : rawRows.all (fun actual =>
    (CompilerCompletion.emitted steps).any (fun expected => decide (
      (Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∨
       Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus (scaleLinear (-1) expected.a)) ∧
      Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b))) = true := by decide
theorem coverage : ∀ actual ∈ rawRows, ∃ expected ∈ CompilerCompletion.emitted steps,
    (Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∨
     Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus (scaleLinear (-1) expected.a)) ∧
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b := by
  intro actual member
  obtain ⟨expected,present,equations⟩ := List.any_eq_true.mp ((List.all_eq_true.mp coverage_checked) actual member)
  exact ⟨expected,present,of_decide_eq_true equations⟩

theorem preserves {{F : Type}} [Field F] (rho : Nat → F) (column : Nat)
    (outside : column ∉ PoseidonCompletion.writes steps) : completeAssignment rho column = rho column :=
  PoseidonCompletion.run_outside rho steps column outside
theorem complete {{F : Type}} [Field F] [CharP F modulus] (rho : Nat → F)
    (linked : rho {copy} = rho 0) : Satisfies (completeAssignment rho) rawRows := by
  have legality : CompilerCompletion.Legal rho steps := by
    simp only [steps,CompilerCompletion.Legal,CompilerCompletion.Step.Legal,and_self]
  have finished := CompilerCompletion.run_complete rho steps kept []
    (ordered [] (by intro row member; cases member)) legality
    (by intro row member; cases member)
  have copyValue : completeAssignment rho {copy} = completeAssignment rho 0 := by
    rw [preserves rho {copy} (by decide),preserves rho 0 (by decide),linked]
  exact CompilerSignedCompletion.original_rows (completeAssignment rho)
    (CompilerCompletion.emitted steps) rawRows {copy} copyValue
    (by simpa only [List.nil_append] using finished) coverage
'''
        exports = ['bounded_checked', 'protected_checked', 'rows_below', 'ordered',
                   'source_chain_checked', 'source_bits_checked', 'endpoint_checked',
                   'coverage_checked', 'coverage', 'preserves', 'complete']
        source += ''.join('#print axioms ' + export + '\n' for export in exports)
        modules[name] = _signature_audits(source + 'end ShielddSecurity.' + name + '\n')
    return modules


def generate(data, extracted, accepted_roles):
    """Symbolic whole canonical255 constructor and derived actual endpoint.

    The written bits have exact Boolean meanings. Bounded product chunks are
    composed using numeric footprints, rather than deciding a wide topological
    checker or assuming the comparator's final state. Original-row transport
    of the reconstruction and endpoint is a separate small boundary below.
    """
    from .generate_hash_round import linear, _signature_audits
    recipe = plan(data, extracted, accepted_roles)
    chunks = recipe['chunks'];names = ['RuntimeTransferAssetMapComparatorConstruction' + str(i) for i in range(len(chunks))]
    copy = recipe['checked']['metadata']['constant_copy'];start = recipe['bits'][0];value = recipe['value']
    name = 'RuntimeTransferAssetMapCanonicalConstruction'
    source = ''.join('import ShielddSecurity.' + n + '\n' for n in names) + '''import ShielddSecurity.ScalarConstructedBits
import ShielddSecurity.ScalarBitFootprint
import ShielddSecurity.CompilerOrderComposition
import ShielddSecurity.TransferReduction
import ShielddSecurity.ScalarChainComposition
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
'''
    source += f'''namespace ShielddSecurity.{name}
-- Exact metadata SHA256 {recipe['checked']['metadata_sha256']}.
-- Direct written-bit meanings; no2^255<modulus or desired endpoint premise.
def modulus : Nat := {maps.P}
def kept : List Nat := {names[0]}.kept
def initialRows : List Row := (List.range' {start} 255).map booleanRow ++
  [reconstructionRow {value} (List.range' {start} 255)]
def programChunks : List (List CompilerCompletion.Step) := [{', '.join(n+'.steps' for n in names)}]
def stages : List CompilerCompletion.Step := programChunks.flatten
def sourceChunks : List (List ScalarRows.StepData) := [{', '.join(n+'.sourceSteps' for n in names)}]
def sourceSteps : List ScalarRows.StepData := sourceChunks.flatten
def commonRows : List Row := initialRows ++ CompilerCompletion.emitted stages
def endpoint : Linear := {linear(recipe['checked']['canonical'][1])}
def prefix0 : List CompilerCompletion.Step := []
'''
    for i, part in enumerate(names):
        source += f'def prefix{i+1} : List CompilerCompletion.Step := prefix{i} ++ {part}.steps\n'
    source += '''theorem stages_exact : stages = prefix32 := by
  simp only [stages,programChunks,List.flatten_cons,List.flatten_nil,'''
    source += ','.join('prefix'+str(i) for i in range(33)) + ''',List.nil_append,List.append_nil,List.append_assoc]

theorem emitted_chunks (chunks : List (List CompilerCompletion.Step)) :
    CompilerCompletion.emitted chunks.flatten = chunks.flatMap CompilerCompletion.emitted := by
  induction chunks with
  | nil => rfl
  | cons chunk tail ih =>
      simp only [List.flatten_cons,List.flatMap_cons,ScalarRandomizerBounds.emitted_append,ih]

theorem ordered : CompilerCompletion.Topological kept initialRows stages := by
'''
    first = names[0]
    source += f'''  have initialized : ScalarRandomizerBounds.RowsBelow {first}.lower initialRows :=
    ScalarBitFootprint.initial_rows_below {value} {start} 255 {first}.lower (by decide) (by decide)
  have below0 : ScalarRandomizerBounds.RowsBelow {first}.lower
      (initialRows ++ CompilerCompletion.emitted prefix0) := by
    simpa only [prefix0,CompilerCompletion.emitted,List.append_nil] using initialized
  have order0 : CompilerCompletion.Topological kept initialRows prefix0 := True.intro
'''
    for i, part in enumerate(names):
        source += f'''  have current{i} := {part}.ordered (initialRows ++ CompilerCompletion.emitted prefix{i}) below{i}
  have order{i+1} : CompilerCompletion.Topological kept initialRows prefix{i+1} :=
    CompilerOrderComposition.append kept initialRows prefix{i} {part}.steps order{i} current{i}
'''
        if i + 1 < len(names):
            next_part = names[i+1]
            source += f'''  have below{i+1} : ScalarRandomizerBounds.RowsBelow {next_part}.lower
      (initialRows ++ CompilerCompletion.emitted prefix{i+1}) := by
    simp only [prefix{i+1},ScalarRandomizerBounds.emitted_append]
    rw [← List.append_assoc]
    exact ScalarRandomizerBounds.rows_append _ _ _
      (ScalarRandomizerBounds.rows_mono {part}.lower {next_part}.lower _ below{i} (by decide))
      (ScalarRandomizerBounds.rows_mono {part}.upper {next_part}.lower _ {part}.rows_below (by decide))
'''
    source += '''  rw [stages_exact]
  exact order32

theorem products : ScalarRandomizerCompletion.Products stages := by
  have prior0 : ScalarRandomizerCompletion.Products prefix0 := True.intro
'''
    for i, part in enumerate(names):
        source += f'''  have current{i} : ScalarRandomizerCompletion.Products {part}.steps := by
    simp only [{part}.steps,ScalarRandomizerCompletion.Products]
  have prior{i+1} : ScalarRandomizerCompletion.Products prefix{i+1} :=
    ScalarRandomizerCompletion.products_append prefix{i} {part}.steps prior{i} current{i}
'''
    source += '''  rw [stages_exact]
  exact prior32

theorem bit_order : sourceSteps.map ScalarRows.StepData.left =
    (List.range' ''' + str(start) + ''' 255).map (fun column => [(column,1)]) := by decide
theorem maximum : binary (sourceSteps.map ScalarRows.StepData.right) = modulus - 1 := by decide
theorem endpoint_exact : ScalarComparisonBounds.endpoint [(0,1)] sourceSteps = endpoint := by rfl
'''
    exports = ['stages_exact', 'emitted_chunks', 'ordered', 'products', 'bit_order', 'maximum', 'endpoint_exact']
    # Exact symbolic inclusion: local Boolean rows enter the initial bit list;
    # material rows enter the flatMap of the already bounded compiler chunks.
    for i, part in enumerate(names):
        # Construct list membership without simplifying reflexive equality to
        # True (which makes an Or/rfl proof depend on simplifier normalization).
        present = '(List.mem_cons_of_mem _ ' * i + 'List.mem_cons_self' + ')' * i
        source += f'''theorem included{i} : ∀ row ∈ {part}.expectedLocalRows, row ∈ commonRows := by
  intro row member
  rcases List.mem_append.mp member with bit | material
  · obtain ⟨column,inside,rfl⟩ := List.mem_map.mp bit
    have allBits : column ∈ List.range' {start} 255 := by
      simp only [List.mem_range'_1] at inside ⊢
      omega
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
      (List.mem_map.mpr ⟨column,allBits,rfl⟩))))
  · apply List.mem_append.mpr
    right
    rw [stages,emitted_chunks]
    apply List.mem_flatMap.mpr
    refine ⟨{part}.steps,?_,material⟩
    change {part}.steps ∈ [{', '.join(n+'.steps' for n in names)}]
    exact {present}
'''
        exports.append('included' + str(i))
    source += '''theorem chain_checked : ScalarRows.checkChain modulus commonRows [(0,1)] sourceSteps = true := by
'''
    for i, part in enumerate(names):
        source += f'''  have chain{i} := ScalarChainComposition.chain_monotone modulus {part}.expectedLocalRows
    commonRows included{i} {part}.initial {part}.sourceSteps {part}.source_chain_checked
'''
    for i in range(len(names)-1):
        source += f'  have boundary{i} : {names[i]}.endpoint = {names[i+1]}.initial := by rfl\n'
    source += '''  apply ScalarChunkComposition.chunks_certificate
  change ScalarChunkComposition.checkChunks modulus commonRows ''' + first + '''.initial sourceChunks = true
  simp only [sourceChunks,ScalarChunkComposition.checkChunks,Bool.and_eq_true,'''
    source += ','.join(n+'.endpoint_checked' for n in names) + ',' + ','.join('boundary'+str(i) for i in range(len(names)-1)) + ''']
  exact ''' + '⟨' * len(names) + ','.join('chain'+str(i) for i in range(len(names))) + ',rfl' + '⟩' * len(names) + '\n'
    # The conjunction above must be nested, not a flat tuple with many commas.
    source = source.replace('⟨' * len(names) + ','.join('chain'+str(i) for i in range(len(names))) + ',rfl' + '⟩' * len(names),
                            ''.join('⟨chain'+str(i)+',' for i in range(len(names)))+'True.intro'+'⟩'*len(names))
    source += '''theorem bits_checked : ScalarBits.checkBits modulus commonRows
    (sourceSteps.map ScalarRows.StepData.left) = true := by
'''
    for i, part in enumerate(names):
        source += f'''  have bits{i} := ScalarChainComposition.bits_monotone modulus {part}.expectedLocalRows
    commonRows included{i} ({part}.sourceSteps.map ScalarRows.StepData.left) {part}.source_bits_checked
'''
    bit_chunks = '[' + ','.join(p+'.sourceSteps.map ScalarRows.StepData.left' for p in names) + ']'
    source += f'''  have collected : ScalarChunkComposition.checkBitChunks modulus commonRows {bit_chunks} = true := by
    simp only [ScalarChunkComposition.checkBitChunks,Bool.and_eq_true]
    exact {''.join('⟨bits'+str(i)+',' for i in range(len(names)))+'True.intro'+'⟩'*len(names)}
  have result := ScalarChunkComposition.bit_chunks_certificate modulus commonRows {bit_chunks} collected
  exact result

variable {{F : Type}} [Field F] [CharP F modulus]
def bitBase (codec : TransferReduction.CanonicalField F) (rho : Nat → F) (nativeValue : F) : Nat → F :=
  writeBits (patchAssignment rho (fun _ => nativeValue) [{value}]) {start} (encodeBits 255 (codec.decode nativeValue))
def completeAssignment (codec : TransferReduction.CanonicalField F)
    (rho : Nat → F) (nativeValue : F) : Nat → F :=
  CompilerCompletion.run (bitBase codec rho nativeValue) stages

theorem common_complete (codec : TransferReduction.CanonicalField F) (rho : Nat → F) (nativeValue : F) :
    Satisfies (completeAssignment codec rho nativeValue) commonRows := by
  have bound : codec.decode nativeValue < 2^255 := Nat.lt_trans (codec.bounded nativeValue) (by decide)
  have meaning : patchAssignment rho (fun _ => nativeValue) [{value}] {value} =
      (codec.decode nativeValue : F) := by
    simp only [patchAssignment,List.mem_singleton,if_true,codec.roundtrip]
  have initialized := writeBits_range_complete (patchAssignment rho (fun _ => nativeValue) [{value}])
    {value} {start} 255 (codec.decode nativeValue) bound meaning (by decide)
  exact CompilerCompletion.run_complete (bitBase codec rho nativeValue) stages kept initialRows ordered
    (ScalarRandomizerCompletion.products_legal _ stages products) initialized

theorem endpoint_value (codec : TransferReduction.CanonicalField F) (rho : Nat → F)
    (nativeValue : F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) :
    eval (completeAssignment codec rho nativeValue) endpoint = 1 := by
  have writtenOne : bitBase codec rho nativeValue 0 = 1 := by
    unfold bitBase
    rw [writeBits_preserves _ _ _ 0 (by simp only [encodeBits_length]; decide)]
    simpa only [patchAssignment,List.mem_singleton,if_neg (by decide : 0 ≠ {value})] using one
  have finalOne : completeAssignment codec rho nativeValue 0 = 1 :=
    (CompilerCompletion.run_preserves (bitBase codec rho nativeValue) stages kept initialRows ordered
      0 (by decide)).trans writtenOne
  have bitOrder : sourceSteps.map ScalarRows.StepData.left =
      (List.range' {start} (encodeBits 255 (codec.decode nativeValue)).length).map
        (fun column => [(column,1)]) := by simpa only [encodeBits_length] using bit_order
  have preserved : ∀ column ∈ List.range' {start} (encodeBits 255 (codec.decode nativeValue)).length,
      completeAssignment codec rho nativeValue column =
        writeBits (patchAssignment rho (fun _ => nativeValue) [{value}]) {start}
          (encodeBits 255 (codec.decode nativeValue)) column := by
    intro column member
    apply CompilerCompletion.run_preserves _ stages kept initialRows ordered
    change column ∈ [0,1,2,{copy},{value}] ++ List.range' {start} 255
    exact List.mem_append.mpr (Or.inr (by simpa only [encodeBits_length] using member))
  have native := ScalarConstructedBits.comparison_from_written_bits
    (patchAssignment rho (fun _ => nativeValue) [{value}]) (completeAssignment codec rho nativeValue)
    {start} (encodeBits 255 (codec.decode nativeValue)) commonRows sourceSteps
    (common_complete codec rho nativeValue) finalOne four bitOrder preserved bits_checked chain_checked
  have bound : codec.decode nativeValue < 2^255 := Nat.lt_trans (codec.bounded nativeValue) (by decide)
  rw [endpoint_exact,encodeBits_value 255 (codec.decode nativeValue) bound,maximum] at native
  have lower : codec.decode nativeValue ≤ modulus - 1 := by
    have below : codec.decode nativeValue < modulus := by
      simpa only [modulus,Scalar.modulus] using codec.bounded nativeValue
    omega
  simpa only [if_pos lower] using native.2
'''
    exports += ['chain_checked', 'bits_checked', 'common_complete', 'endpoint_value']
    boundary_indices = [recipe['boundaries'][label] for label in ('reconstruction', 'endpoint', 'link')]
    source += f'''
-- This exact partition is checked against the selected original row index set
-- by the maintained generator. The data order is component order; all physical
-- row indices and original boundary coefficients remain explicit.
def originalRowIndices : List Nat := {recipe['original_partition']}
def booleanRowIndices : List Nat := {recipe['boolean_indices']}
def boundaryRowIndices : List Nat := {boundary_indices}
def productOriginalChunks : List (List Row) := [{','.join(n+'.rawRows' for n in names)}]
def boundaryRawRows : List Row := [
''' + ',\n'.join('⟨'+linear(recipe['raw'][i][0])+','+linear(recipe['raw'][i][1])+'⟩' for i in boundary_indices) + f''']
def boundaryExpected : List Row := [reconstructionRow {value} (List.range' {start} 255),
  ⟨Compiler.subtract endpoint [(0,1)],[]⟩,⟨[],[]⟩]
def rawRows : List Row := (List.range' {start} 255).map booleanRow ++
  (productOriginalChunks.flatten ++ boundaryRawRows)

theorem boundary_coverage_checked : boundaryRawRows.all (fun actual =>
    boundaryExpected.any (fun expected => decide (
      (Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∨
       Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus (scaleLinear (-1) expected.a)) ∧
      Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b))) = true := by decide
theorem boundary_coverage : ∀ actual ∈ boundaryRawRows, ∃ expected ∈ boundaryExpected,
    (Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∨
     Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus (scaleLinear (-1) expected.a)) ∧
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b := by
  intro actual member
  obtain ⟨expected,present,equations⟩ := List.any_eq_true.mp ((List.all_eq_true.mp boundary_coverage_checked) actual member)
  exact ⟨expected,present,of_decide_eq_true equations⟩

theorem preserves (codec : TransferReduction.CanonicalField F) (rho : Nat → F)
    (nativeValue : F) (column : Nat) (rootOutside : column ≠ {value})
    (bitsOutside : column < {start} ∨ {start} + 255 ≤ column)
    (productsOutside : column ∉ PoseidonCompletion.writes stages) :
    completeAssignment codec rho nativeValue column = rho column := by
  unfold completeAssignment bitBase
  rw [PoseidonCompletion.run_outside _ stages column productsOutside]
  rw [writeBits_preserves _ _ _ column (by simpa only [encodeBits_length] using bitsOutside)]
  simp only [patchAssignment,List.mem_singleton,if_neg rootOutside]

theorem complete_rows (codec : TransferReduction.CanonicalField F) (rho : Nat → F)
    (nativeValue : F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (linked : rho {copy} = rho 0) : Satisfies (completeAssignment codec rho nativeValue) rawRows := by
  let finished := completeAssignment codec rho nativeValue
  have common := common_complete codec rho nativeValue
  have finalZero : finished 0 = rho 0 := preserves codec rho nativeValue 0 (by decide) (by decide) (by decide)
  have finalCopy : finished {copy} = rho {copy} := preserves codec rho nativeValue {copy} (by decide) (by decide) (by decide)
  have copyLink : finished {copy} = finished 0 := by rw [finalCopy,finalZero,linked]
  have endpointValue : eval finished endpoint = 1 := endpoint_value codec rho nativeValue one four
  have boundaryExpectedComplete : Satisfies finished boundaryExpected := by
    intro row member
    simp only [boundaryExpected,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact common _ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (by simp)))))
    · simp only [Square,Compiler.eval_subtract,endpointValue,eval,Int.cast_one,one,finalZero,
        one_mul,add_zero,sub_self,zero_mul]
    · simp only [Square,eval,zero_mul]
  have boundaryComplete : Satisfies finished boundaryRawRows :=
    CompilerSignedCompletion.original_rows finished boundaryExpected boundaryRawRows {copy}
      copyLink boundaryExpectedComplete boundary_coverage
'''
    for i, part in enumerate(names):
        source += f'''  have products{i} : Satisfies finished {part}.rawRows :=
    CompilerSignedCompletion.original_rows finished (CompilerCompletion.emitted {part}.steps)
      {part}.rawRows {copy} copyLink
      (by intro row member; exact common row (included{i} row (List.mem_append.mpr (Or.inr member))))
      {part}.coverage
'''
    source += '''  intro row member
  simp only [rawRows,List.mem_append] at member
  rcases member with bit | product | boundary
  · exact common row (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl bit))))
  · obtain ⟨chunk,present,inside⟩ := List.mem_flatten.mp product
    simp only [productOriginalChunks,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with ''' + ' | '.join('rfl' for _ in names) + '\n'
    source += ''.join('    · exact products'+str(i)+' row inside\n' for i in range(len(names)))
    source += '  · exact boundaryComplete row boundary\n'
    exports += ['boundary_coverage_checked', 'boundary_coverage', 'preserves', 'complete_rows']
    source += ''.join('#print axioms ' + export + '\n' for export in exports)
    return name, _signature_audits(source + 'end ShielddSecurity.' + name + '\n')
