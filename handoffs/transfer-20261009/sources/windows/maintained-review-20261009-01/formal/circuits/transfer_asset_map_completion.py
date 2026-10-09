"""Strict actual-map ownership and constructive witness/materialization plan.

The executable field constructor is a small semantic test of the plan, not a
Lean completeness certificate. It takes a native sqrt operation and checks its
field-level specification at every invocation. Formal native sqrt/codec/curve
contracts and derivation of the final assertion phase remain separate joins.
All original selected rows, including deferred asserted squares, are retained.
"""
from . import transfer_asset_map as maps, transfer_arithmetic as arithmetic
from . import transfer_relation as relation
from .transfer_balance_rows import canonical, combine


def _unit(lc, label):
    if len(lc) != 1 or lc[0][1] != 1 or lc[0][0] == 0:
        raise relation.RelationError('map completion exact unit witness/pivot: ' + label)
    return lc[0][0]


def plan(data, extracted, accepted_roles):
    result = maps.certificates(data, extracted, accepted_roles)
    checked, rows, raw = result['checked'], result['rows'], result['raw']
    v = checked['values']
    seed_lcs = [('firstInverse', v['inv1']), ('choice', v['square']),
                ('qrRoot', v['qr_root']), ('selectedRoot', v['y']),
                ('zero', v['zero']), ('totalInverse', v['inv'])]
    seed_lcs += [('doubleInverse' + str(i), a[6]) for i, a in enumerate(checked['auxiliary'])]
    seed_lcs += [('bit' + str(i), bit) for i, bit in enumerate(checked['bits'])]
    seeds = {label: _unit(lc, label) for label, lc in seed_lcs}
    if len(set(seeds.values())) != len(seeds):
        raise relation.RelationError('map completion seed witness alias')
    shared = [maps.ONE, ((1, 1),), ((2, 1),),
              ((checked['metadata']['constant_copy'], 1),), checked['asset'], checked['hash'], v['u']]
    shared += list(accepted_roles['observed'].values())
    kept = sorted({c for lc in shared for c, _ in lc})
    if set(kept) & set(seeds.values()):
        raise relation.RelationError('map completion seeds affect shared input/caller roles')
    known = set(kept) | set(seeds.values())
    source_witnesses = {c for handle, lc in checked['captured_observed'].items() if handle[0] == 1
                        for c, _ in lc}
    if not source_witnesses <= known:
        raise relation.RelationError('map completion unclassified native witness')

    # Deduplicate the same physical pair observed both as a source product and
    # as a division constraint; never allocate either compiler column twice.
    candidates = []
    seen = set()
    for (node, a, b, output), certificate in zip(checked['nonlinear'], result['nonlinear']):
        key = tuple(certificate['rows'])
        if key in seen:
            continue
        seen.add(key)
        candidates.append(dict(node=node, left=a, right=b, output=output, certificate=certificate))
    for i, certificate in enumerate(result['quotients']):
        if certificate['kind'] not in ('product', 'square'):
            raise relation.RelationError('map completion quotient lowering unsupported')
        count = 2 if certificate['kind'] == 'product' else 1
        key = tuple(certificate['rows'][:count])
        if key in seen:
            continue
        seen.add(key)
        candidates.append(dict(node='inverse' + str(i), left=certificate['quotient'],
                               right=certificate['denominator'], output=certificate['output'],
                               certificate=dict(certificate, rows=list(key))))
    steps, material_rows, owned = [], set(), set(seeds.values())
    pending = list(candidates)
    while pending:
        progress = False
        for candidate in list(pending):
            cert = candidate['certificate']
            a, b, output = candidate['left'], candidate['right'], candidate['output']
            if cert.get('swapped'):
                a, b = b, a
            reads = {c for c, _ in a + b}
            if not reads <= known:
                continue
            pivots = [c for c, n in output if n == 1 and c not in known]
            if len(pivots) > 1:
                raise relation.RelationError('map completion ambiguous materialized unit pivot')
            remainder = tuple((c, n) for c, n in output if not pivots or c != pivots[0])
            if not {c for c, _ in remainder} <= known:
                continue
            if cert['kind'] == 'square':
                if pivots:
                    pivot = pivots[0]
                    steps.append(dict(kind='square', input=a, remainder=remainder, output=pivot,
                                      writes=[pivot], rows=cert['rows'], source=candidate['node']))
                    material_rows.update(cert['rows']);known.add(pivot);owned.add(pivot)
                # With no pivot this is a real deferred asserted-square row.
                # It is emitted in the final assertion phase, never invented
                # as a materialized output or given an output LC by the compiler.
            elif cert['kind'] == 'product':
                auxiliary = _unit(cert['auxiliary'], 'product auxiliary')
                if auxiliary in known or auxiliary in owned:
                    raise relation.RelationError('map completion compiler auxiliary aliases prior/shared column')
                if pivots:
                    pivot = pivots[0]
                    if pivot == auxiliary:
                        raise relation.RelationError('map completion product/auxiliary alias')
                    steps.append(dict(kind='product', left=a, right=b, remainder=remainder,
                                      output=pivot, auxiliary=auxiliary, writes=[pivot, auxiliary],
                                      rows=cert['rows'], source=candidate['node']))
                    material_rows.update(cert['rows']);known.add(pivot);owned.add(pivot)
                else:
                    # Fused numerator/constant products use the original
                    # difference-square auxiliary and a final sum-square row.
                    steps.append(dict(kind='square', input=combine(a, b, -1), remainder=(),
                                      output=auxiliary, writes=[auxiliary], rows=cert['rows'][:1],
                                      source=candidate['node']))
                    material_rows.add(cert['rows'][0])
                known.add(auxiliary);owned.add(auxiliary)
            else:
                raise relation.RelationError('map completion source product lowering unsupported')
            pending.remove(candidate);progress = True
        if not progress:
            raise relation.RelationError('map completion source reads unresolved/fused output dependency')

    copy = checked['metadata']['constant_copy']
    links = [i for i, row in raw.items() if row == (canonical([(0, 1), (copy, -1)]), ())]
    if len(links) != 1:
        raise relation.RelationError('map completion exact constant-copy link')
    assertions = [dict(row=i, left=a, right=b) for i, (a, b) in rows.items()
                  if i not in material_rows and i not in links]
    if any(c not in known for entry in assertions for c, _ in entry['left'] + entry['right']):
        raise relation.RelationError('map completion final assertion uses unowned column')
    if len(material_rows) + len(assertions) + 1 != len(raw):
        raise relation.RelationError('map completion complete original-row partition')
    # The incremental allocator is also an independent support/freshness check.
    prior = set()
    for step in steps:
        writes = set(step['writes'])
        reads = set(c for lc in ([step['input']] if step['kind'] == 'square'
                                else [step['left'], step['right']]) + [step['remainder']] for c, _ in lc)
        if writes & (reads | prior | set(kept) | set(seeds.values())):
            raise relation.RelationError('map completion materialization order/freshness failed')
        prior.update(c for i in step['rows'] for lc in rows[i] for c, _ in lc)
    return dict(checked=checked, raw=raw, normalized=rows, seeds=seeds, kept=kept,
                owned_writes=sorted(owned), steps=steps, assertion_rows=assertions,
                material_rows=sorted(material_rows), link_row=links[0])


def construct(data, extracted, accepted_roles, base, sqrt):
    """Execute the exact owned plan using native field sqrt/encoding semantics.

    This returns a bounded runtime construction check. It is deliberately not a
    formal certificate or a claim that surrounding/full Transfer rows survive.
    """
    recipe = plan(data, extracted, accepted_roles)
    p = maps.P
    rho = dict(base)
    evaluate = lambda lc: sum(rho.get(c, 0) * n for c, n in lc) % p
    if rho.get(0) != 1 or rho.get(recipe['checked']['metadata']['constant_copy']) != 1:
        raise relation.RelationError('map completion kept native constant/copy must be one')

    def root(value):
        value %= p
        result = sqrt(value)
        exists = value == 0 or pow(value, (p - 1) // 2, p) == 1
        if (result is not None) != exists or result is not None and (
                type(result) is not int or not 0 <= result < p or result * result % p != value):
            raise relation.RelationError('map completion native sqrt/option specification')
        return result

    u = evaluate(recipe['checked']['values']['u'])
    tv = 5 * u * u % p
    if (1 + tv) % p == 0:
        raise relation.RelationError('map completion native first denominator impossible')
    first_inverse = pow(1 + tv, -1, p)
    x1 = -maps.C1 * first_inverse % p
    gx1 = ((x1 + maps.C1) * x1 + maps.C2) * x1 % p
    first_root = root(gx1)
    option = first_root is not None
    qr_root = first_root if option else root(5 * gx1)
    x = x1 if option else (-x1 - maps.C1) % p
    selected_root = first_root if option else root(tv * gx1)
    if qr_root is None or selected_root is None:
        raise relation.RelationError('map completion native alternative sqrt unavailable')
    if selected_root % 2 != int(option):
        selected_root = -selected_root % p
    s, t = x * maps.K % p, selected_root * maps.K % p
    den = (s + 1) * t % p
    inv = pow(den, -1, p) if den else 0
    zero = int(den == 0)
    point = (inv * (s + 1) * s % p, (inv * t * (s - 1) + zero) % p)
    seed_values = dict(firstInverse=first_inverse, choice=int(option), qrRoot=qr_root,
                       selectedRoot=selected_root, zero=zero, totalInverse=inv)
    for stage in range(3):
        xx, yy = point[0]**2 % p, point[1]**2 % p
        delta = maps.D * xx * yy % p
        divisor = (1 + delta) * (1 - delta) % p
        if not divisor:
            raise relation.RelationError('map completion native complete-curve denominator impossible')
        inverse = pow(divisor, -1, p)
        seed_values['doubleInverse' + str(stage)] = inverse
        point = (2 * point[0] * point[1] * (1 - delta) * inverse % p,
                 (xx + yy) * (1 + delta) * inverse % p)
    seed_values.update({'bit' + str(i): selected_root >> i & 1 for i in range(255)})
    for label, column in recipe['seeds'].items():
        rho[column] = seed_values[label]
    for step in recipe['steps']:
        remainder = evaluate(step['remainder'])
        if step['kind'] == 'square':
            value = evaluate(step['input'])**2 - remainder
        else:
            a, b = evaluate(step['left']), evaluate(step['right'])
            value = a * b - remainder
            rho[step['auxiliary']] = (a - b)**2 % p
        rho[step['output']] = value % p
    for index, (a, b) in recipe['raw'].items():
        if evaluate(a)**2 % p != evaluate(b):
            raise relation.RelationError('map completion original row failed: ' + str(index))
    if any(rho.get(c, 0) != value for c, value in base.items() if c not in recipe['owned_writes']):
        raise relation.RelationError('map completion modified column outside exact ownership')
    return dict(assignment=rho, plan=recipe, native_image=point,
                proof=False, scope='bounded exact original map row construction; full Transfer/native ABI open')


def generate_materializations(data, extracted, accepted_roles, *, chunk_size=8):
    """Unconditional original-row completion of bounded allocation chunks.

    These are numeric materializations only. The native-seeded Boolean,
    comparator endpoint, parity, inverse assertions and fused asserted-square
    phase are recorded in the plan and are not smuggled into Legal premises.
    """
    from .generate_hash_round import linear, _signature_audits
    if type(chunk_size) is not int or not 1 <= chunk_size <= 16:
        raise relation.RelationError('map completion materialization chunk bound')
    recipe = plan(data, extracted, accepted_roles)
    modules = {}
    copy = recipe['checked']['metadata']['constant_copy']
    for start in range(0, len(recipe['steps']), chunk_size):
        chunk = recipe['steps'][start:start + chunk_size]
        name = 'RuntimeTransferAssetMapMaterialization' + str(start // chunk_size)
        writes = {column for step in chunk for column in step['writes']}
        kept = set(recipe['kept']) | set(recipe['seeds'].values())
        kept.update(c for step in chunk for lc in
                    (([step['input']] if step['kind'] == 'square' else [step['left'], step['right']]) +
                     [step['remainder']]) for c, _ in lc if c not in writes)
        indices = sorted({index for step in chunk for index in step['rows']})
        steps = []
        for step in chunk:
            if step['kind'] == 'square':
                steps.append('.square ' + linear(step['input']) + ' ' + linear(step['remainder']) +
                             ' ' + str(step['output']))
            else:
                steps.append('.product ' + linear(step['left']) + ' ' + linear(step['right']) +
                             ' ' + linear(step['remainder']) + ' ' + str(step['output']) +
                             ' ' + str(step['auxiliary']))
        source = f'''import ShielddSecurity.CompilerOrder
import ShielddSecurity.CompilerSignedCompletion
import ShielddSecurity.PoseidonCompletion
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
namespace ShielddSecurity.{name}
-- Exact map metadata SHA256 {recipe['checked']['metadata_sha256']}.
-- Only numeric allocation rows; the native seed/assertion phase and full map remain open.
def modulus : Nat := {maps.P}
def originalRows : List Nat := {indices}
def rawRows : List Row := [
''' + ',\n'.join('⟨' + linear(recipe['raw'][i][0]) + ',' + linear(recipe['raw'][i][1]) + '⟩'
                 for i in indices) + ''']
def steps : List CompilerCompletion.Step := [
''' + ',\n'.join(steps) + f''']
def kept : List Nat := {sorted(kept)}
def ownedWrites : List Nat := PoseidonCompletion.writes steps
def completeAssignment {{F : Type}} [Field F] (rho : Nat → F) : Nat → F :=
  CompilerCompletion.run rho steps

theorem ordered_checked : CompilerOrder.checkOrder kept [] steps = true := by decide
theorem ordered : CompilerCompletion.Topological kept [] steps :=
  CompilerOrder.checked_order kept [] steps ordered_checked

theorem legal {{F : Type}} [Field F] (rho : Nat → F) : CompilerCompletion.Legal rho steps := by
  simp only [steps,CompilerCompletion.Legal,CompilerCompletion.Step.Legal,and_self]

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
    (outside : column ∉ ownedWrites) : completeAssignment rho column = rho column :=
  PoseidonCompletion.run_outside rho steps column outside

theorem complete {{F : Type}} [Field F] [CharP F modulus] (rho : Nat → F)
    (linked : rho {copy} = rho 0) : Satisfies (completeAssignment rho) rawRows := by
  have completed := CompilerCompletion.run_complete rho steps kept [] ordered (legal rho)
    (by intro row member; cases member)
  have copyValue : completeAssignment rho {copy} = completeAssignment rho 0 := by
    rw [preserves rho {copy} (by decide),preserves rho 0 (by decide),linked]
  exact CompilerSignedCompletion.original_rows (completeAssignment rho)
    (CompilerCompletion.emitted steps) rawRows {copy} copyValue
    (by simpa only [List.nil_append] using completed) coverage
'''
        exports = ['ordered_checked', 'ordered', 'legal', 'coverage_checked', 'coverage', 'preserves', 'complete']
        source += ''.join('#print axioms ' + export + '\n' for export in exports)
        modules[name] = _signature_audits(source + 'end ShielddSecurity.' + name + '\n')
    return modules


def generate_native_bits(data, extracted, accepted_roles):
    """Construct the real255-bit block/reconstruction from a native field value.

    The codec supplies its canonical integer; no desired reconstruction value
    or bit bound is a premise. Numeric stages explicitly keep all these seeds.
    """
    from .generate_hash_round import linear, _signature_audits
    recipe = plan(data, extracted, accepted_roles)
    columns = [recipe['seeds']['bit' + str(i)] for i in range(255)]
    start, value = columns[0], recipe['seeds']['selectedRoot']
    if columns != list(range(start, start + 255)) or start <= value < start + 255:
        raise relation.RelationError('map native bits contiguous fresh original witnesses')
    booleans = []
    indices = []
    for column in columns:
        matches = [(index, row) for index, row in recipe['raw'].items()
                   if row == (((column, 1),), ((column, 1),))]
        if len(matches) != 1:
            raise relation.RelationError('map native bits exact unsigned Boolean row')
        index, row = matches[0];indices.append(index);booleans.append(row)
    weighted = canonical((column, 2**i) for i, column in enumerate(columns))
    difference = combine(weighted, ((value, 1),), -1)
    matches = [(index, row) for index, row in recipe['normalized'].items()
               if row in ((difference, ()), (maps._scale(difference, -1), ()))]
    if len(matches) != 1:
        raise relation.RelationError('map native bits exact reconstruction assertion')
    reconstruction_index = matches[0][0]
    actual = recipe['raw'][reconstruction_index]
    copy = recipe['checked']['metadata']['constant_copy']
    name = 'RuntimeTransferAssetMapNativeBits'
    source = f'''import ShielddSecurity.CompilerSignedCompletion
import ShielddSecurity.TransferReduction
set_option maxHeartbeats 300000
set_option maxRecDepth 2048
namespace ShielddSecurity.{name}
-- Exact source metadata SHA256 {recipe['checked']['metadata_sha256']}.
-- Construct native root/canonical255-bit witnesses only; parity/comparator/full map composed separately.
def modulus : Nat := {maps.P}
def originalBooleanRows : List Nat := {indices}
def originalReconstructionRow : Nat := {reconstruction_index}
def rawBooleanRows : List Row := [
''' + ',\n'.join('⟨' + linear(a) + ',' + linear(b) + '⟩' for a, b in booleans) + f''']
def rawReconstructionRow : Row := ⟨{linear(actual[0])},{linear(actual[1])}⟩
def rawRows : List Row := rawBooleanRows ++ [rawReconstructionRow]
def seedValue {{F : Type}} [Field F] (rho : Nat → F) (nativeValue : F) : Nat → F :=
  patchAssignment rho (fun _ => nativeValue) [{value}]
def completeAssignment {{F : Type}} [Field F] [CharP F modulus]
    (codec : TransferReduction.CanonicalField F) (rho : Nat → F) (nativeValue : F) : Nat → F :=
  writeBits (seedValue rho nativeValue) {start} (encodeBits 255 (codec.decode nativeValue))

theorem booleans_checked : rawBooleanRows = (List.range' {start} 255).map booleanRow := by decide

theorem reconstruction_checked :
    (Compiler.canonical modulus (Compiler.unoutline {copy} rawReconstructionRow.a) =
       Compiler.canonical modulus (reconstructionRow {value} (List.range' {start} 255)).a ∨
     Compiler.canonical modulus (Compiler.unoutline {copy} rawReconstructionRow.a) =
       Compiler.canonical modulus (scaleLinear (-1) (reconstructionRow {value} (List.range' {start} 255)).a)) ∧
    Compiler.canonical modulus (Compiler.unoutline {copy} rawReconstructionRow.b) =
       Compiler.canonical modulus (reconstructionRow {value} (List.range' {start} 255)).b := by decide

theorem preserves {{F : Type}} [Field F] [CharP F modulus]
    (codec : TransferReduction.CanonicalField F) (rho : Nat → F) (nativeValue : F) (column : Nat)
    (outsideRoot : column ≠ {value}) (outsideBits : column < {start} ∨ {start}+255 ≤ column) :
    completeAssignment codec rho nativeValue column = rho column := by
  unfold completeAssignment
  rw [writeBits_preserves _ _ _ column (by simpa only [encodeBits_length] using outsideBits)]
  exact patchAssignment_preserves rho (fun _ => nativeValue) [{value}] column
    (by simpa only [List.mem_singleton] using outsideRoot)

theorem complete {{F : Type}} [Field F] [CharP F modulus]
    (codec : TransferReduction.CanonicalField F) (rho : Nat → F) (nativeValue : F)
    (linked : rho {copy} = rho 0) : Satisfies (completeAssignment codec rho nativeValue) rawRows := by
  have bound : codec.decode nativeValue < 2^255 :=
    (codec.bounded nativeValue).trans (by decide : Scalar.modulus < 2^255)
  have meaning : seedValue rho nativeValue {value} = ((codec.decode nativeValue : Nat) : F) := by
    simp only [seedValue,patchAssignment,List.mem_singleton,if_pos rfl]
    exact (codec.roundtrip nativeValue).symm
  have expected := writeBits_range_complete (seedValue rho nativeValue) {value} {start} 255
    (codec.decode nativeValue) bound meaning (by decide)
  have copyLink : completeAssignment codec rho nativeValue {copy} = completeAssignment codec rho nativeValue 0 := by
    rw [preserves codec rho nativeValue {copy} (by decide) (by decide),
      preserves codec rho nativeValue 0 (by decide) (by decide),linked]
  intro row member
  rcases List.mem_append.mp member with boolean | assertion
  · rw [booleans_checked] at boolean
    exact expected row (List.mem_append_left _ boolean)
  · simp only [List.mem_singleton] at assertion
    subst row
    have valid := expected (reconstructionRow {value} (List.range' {start} 255))
      (List.mem_append_right _ (by simp only [List.mem_singleton]))
    have original := CompilerSignedCompletion.signed_row
      (completeAssignment codec rho nativeValue)
      (⟨Compiler.unoutline {copy} rawReconstructionRow.a,
        Compiler.unoutline {copy} rawReconstructionRow.b⟩ : Row)
      (reconstructionRow {value} (List.range' {start} 255))
      reconstruction_checked.1 reconstruction_checked.2 valid
    simpa only [Compiler.eval_unoutline (completeAssignment codec rho nativeValue) {copy} _ copyLink] using original
'''
    exports = ['booleans_checked', 'reconstruction_checked', 'preserves', 'complete']
    source += ''.join('#print axioms ' + export + '\n' for export in exports)
    return name, _signature_audits(source + 'end ShielddSecurity.' + name + '\n')
