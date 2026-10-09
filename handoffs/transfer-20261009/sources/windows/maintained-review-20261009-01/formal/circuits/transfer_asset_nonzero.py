"""Four ordinary Transfer rows proving asset nonzero at the pinned boundary.

The stream check establishes exact serialized-row identity. The emitted Lean
candidate proves the row implication for any satisfying assignment. Caller LC
correspondence, native semantics, full Transfer and certification remain open.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

from . import transfer_relation as relation
from .generate_hash_round import _signature_audits, linear

P = relation.MODULUS
RELATION_DIGEST = '16e7b009b763be55ca21f423f4f97e8c132b40b6adbcd06f6a3be17f2d0ef236'
RAW_SHA256 = 'fa0de5dba3cc2b75ea56e333d2c60f8b373f0c59f6f9b4aed04fd2f59b7f2c9f'
ASSET, INVERSE, PRODUCT, AUXILIARY, CONSTANT_COPY = 6, 1992, 49790, 49791, 200692
ROW_INDICES = (27052, 27053, 179944, 200769)
SCOPE = ('four actual asset-inverse/product/assertion/constant-link rows only; '
         'caller LC correspondence, native interpretation and full Transfer open')
SCHEMA = 'shieldd-transfer-asset-nonzero-rows-v1'
COMPLETION_WRITES = (INVERSE, PRODUCT, AUXILIARY, CONSTANT_COPY)
EXPORTS = ('constantLink', 'inverse_equation', 'asset_nonzero', 'inverse_square_completion',
           'complete_preserves', 'complete_preserves_roles', 'complete_satisfies', 'local_completion')


def _terms(values):
    return [[column, f'{coefficient % P:064x}'] for column, coefficient in sorted(values)]


def _expected_rows():
    # Row 179944 is copy - product, not product - copy. Keep actual orientation.
    return [
        dict(row=ROW_INDICES[0], a=_terms([(INVERSE, 1), (ASSET, -1)]),
             b=_terms([(AUXILIARY, 1)])),
        dict(row=ROW_INDICES[1], a=_terms([(INVERSE, 1), (ASSET, 1)]),
             b=_terms([(PRODUCT, 4), (AUXILIARY, 1)])),
        dict(row=ROW_INDICES[2], a=_terms([(CONSTANT_COPY, 1), (PRODUCT, -1)]), b=[]),
        dict(row=ROW_INDICES[3], a=_terms([(0, 1), (CONSTANT_COPY, -1)]), b=[]),
    ]


def _validate(extracted):
    if (not isinstance(extracted, dict) or
            set(extracted) != {'schema', 'identity', 'selected_rows', 'scope'} or
            extracted['schema'] != SCHEMA or extracted['scope'] != SCOPE):
        raise relation.RelationError('unknown asset-nonzero extraction schema/scope')
    identity = extracted['identity']
    identity_keys = {'schema', 'domain_size', 'stored_rows', 'relation_digest',
                     'raw_sha256', 'source_public', 'source_blocks', 'scope'}
    if (not isinstance(identity, dict) or set(identity) != identity_keys or
            identity['schema'] != 'shieldd-transfer-relation-v1' or
            type(identity['domain_size']) is not int or identity['domain_size'] != 262144 or
            type(identity['stored_rows']) is not int or identity['stored_rows'] != 200770 or
            identity['relation_digest'] != RELATION_DIGEST or
            identity['raw_sha256'] != RAW_SHA256 or
            identity['source_public'] != [[1, 22734]] or
            identity['source_blocks'] != [[[1, 6]]]):
        raise relation.RelationError('asset-nonzero ordinary relation identity mismatch')
    relation.indices(identity['source_public'])
    relation.indices(identity['source_blocks'][0])
    rows = extracted['selected_rows']
    if not isinstance(rows, list) or len(rows) != 4:
        raise relation.RelationError('asset-nonzero requires exactly four ordinary rows')
    for row in rows:
        if not isinstance(row, dict) or set(row) != {'row', 'a', 'b'}:
            raise relation.RelationError('malformed asset-nonzero ordinary row')
        relation.natural(row['row'], identity['stored_rows'])
        relation.terms(row['a'], identity['domain_size'])
        relation.terms(row['b'], identity['domain_size'])
    if rows != _expected_rows():
        raise relation.RelationError('asset-nonzero exact row/operand orientation mismatch')
    return rows


def inspect(stream):
    """Consume and digest-check the entire ordinary relation before selecting."""
    selected = []

    def observe(row):
        if row['row'] in ROW_INDICES:
            selected.append(row)

    identity = relation.inspect(stream, RELATION_DIGEST, observe)
    extracted = dict(schema=SCHEMA, identity=identity, selected_rows=selected, scope=SCOPE)
    _validate(extracted)
    return extracted


def from_extraction_bytes(data, expected_sha256):
    """Revalidate exact retained extraction bytes; requires its accepted receipt.

    The supplied hash preserves input identity, not semantic correspondence.
    This path does not repeat the original whole-relation streaming check.
    """
    if (not isinstance(expected_sha256, str) or
            not re.fullmatch('[0-9a-f]{64}', expected_sha256)):
        raise relation.RelationError('exact retained extraction SHA256 required')
    if not isinstance(data, bytes) or len(data) > 65536:
        raise relation.RelationError('retained asset extraction exceeds bounded byte schema')
    if hashlib.sha256(data).hexdigest() != expected_sha256:
        raise relation.RelationError('retained asset extraction byte identity mismatch')
    extracted = relation.record(data)
    _validate(extracted)
    return extracted


def generate(extracted):
    """Emit row soundness and constructive completion for only these rows."""
    selected = _validate(extracted)

    def parse(terms):
        return tuple((column, int(encoded, 16)) for column, encoded in terms)

    source = f'''import ShielddSecurity.Compiler
set_option maxHeartbeats 500000
namespace ShielddSecurity.RuntimeTransferAssetNonzero
-- Actual ordinary relation: {RELATION_DIGEST}
-- {SCOPE}.
def modulus : Nat := {P}
def originalRows : List Nat := {list(ROW_INDICES)}
def rawRows : List Row := [
'''
    source += ',\n'.join('  ⟨' + linear(parse(row['a'])) + ', ' + linear(parse(row['b'])) + '⟩'
                          for row in selected) + ']\n'
    source += f'''def asset : Linear := [({ASSET}, 1)]
def inverse : Linear := [({INVERSE}, 1)]
def product : Linear := [({PRODUCT}, 1)]
def auxiliary : Linear := [({AUXILIARY}, 1)]
def rows : List Row := Compiler.unoutlineRows {CONSTANT_COPY} rawRows

theorem constantLink : Compiler.checkRow modulus rawRows
    ⟨[(0, 1), ({CONSTANT_COPY}, -1)], []⟩ = true := by decide

theorem inverse_equation {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    eval rho inverse * eval rho asset = 1 := by
  have normalized : Satisfies rho rows :=
    Compiler.unoutline_rows_sound rho {CONSTANT_COPY} rawRows satisfied constantLink
  have multiplied := Compiler.checked_product_sound rho rows inverse asset
    product auxiliary four normalized (by decide) (by decide)
  have asserted := Compiler.checked_assertion_sound rho rows [(0, 1)] product
    normalized (by decide)
  exact multiplied.symm.trans (asserted.symm.trans (by simp [eval, one]))

theorem asset_nonzero {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) : eval rho asset ≠ 0 := by
  intro zero
  have equation := inverse_equation rho one four satisfied
  rw [zero, mul_zero] at equation
  exact zero_ne_one equation

-- Local legal-input completion only: these four writes may affect other
-- Transfer rows. No theorem here asserts their preservation.
def completionWrites : List Nat := {list(COMPLETION_WRITES)}
def completeAssignment {{F : Type}} [Field F] (rho : Nat → F) : Nat → F :=
  fun column =>
    if column = {INVERSE} then (rho {ASSET})⁻¹
    else if column = {PRODUCT} then 1
    else if column = {AUXILIARY} then ((rho {ASSET})⁻¹ - rho {ASSET}) ^ 2
    else if column = {CONSTANT_COPY} then 1
    else rho column

theorem inverse_square_completion {{F : Type}} [Field F]
    (value : F) (nonzero : value ≠ 0) :
    (value⁻¹ + value) * (value⁻¹ + value) = 4 + (value⁻¹ - value) ^ 2 := by
  have inverse : value⁻¹ * value = 1 := inv_mul_cancel₀ nonzero
  calc
    _ = 4 * (value⁻¹ * value) + (value⁻¹ - value) ^ 2 := by ring
    _ = _ := by rw [inverse]; ring

theorem complete_preserves {{F : Type}} [Field F] (rho : Nat → F)
    (column : Nat) (untouched : column ∉ completionWrites) :
    completeAssignment rho column = rho column := by
  have exclusions : column ≠ {INVERSE} ∧ column ≠ {PRODUCT} ∧
      column ≠ {AUXILIARY} ∧ column ≠ {CONSTANT_COPY} := by
    simpa [completionWrites] using untouched
  rcases exclusions with ⟨inverseNe, productNe, auxiliaryNe, copyNe⟩
  simp only [completeAssignment, if_neg inverseNe, if_neg productNe,
    if_neg auxiliaryNe, if_neg copyNe]

theorem complete_preserves_roles {{F : Type}} [Field F] (rho : Nat → F) :
    completeAssignment rho 0 = rho 0 ∧ completeAssignment rho 1 = rho 1 ∧
      completeAssignment rho 2 = rho 2 ∧ completeAssignment rho {ASSET} = rho {ASSET} := by
  exact ⟨complete_preserves rho 0 (by decide), complete_preserves rho 1 (by decide),
    complete_preserves rho 2 (by decide), complete_preserves rho {ASSET} (by decide)⟩

theorem complete_satisfies {{F : Type}} [Field F] (rho : Nat → F)
    (one : rho 0 = 1) (nonzero : rho {ASSET} ≠ 0) :
    Satisfies (completeAssignment rho) rawRows := by
  intro row member
  simp only [rawRows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · simp [Square, eval, completeAssignment, pow_two] <;> ring
  · simpa [Square, eval, completeAssignment, add_comm] using
      inverse_square_completion (rho {ASSET}) nonzero
  · simp [Square, eval, completeAssignment]
  · simp [Square, eval, completeAssignment, one]

theorem local_completion {{F : Type}} [Field F] (rho : Nat → F)
    (one : rho 0 = 1) (nonzero : rho {ASSET} ≠ 0) :
    ∃ completed : Nat → F, Satisfies completed rawRows ∧
      (∀ column, column ∉ completionWrites → completed column = rho column) ∧
      completed 0 = rho 0 ∧ completed 1 = rho 1 ∧ completed 2 = rho 2 ∧
      completed {ASSET} = rho {ASSET} := by
  exact ⟨completeAssignment rho, complete_satisfies rho one nonzero,
    complete_preserves rho, complete_preserves_roles rho⟩
'''
    source += ''.join(f'#print axioms {name}\n' for name in EXPORTS)
    source += 'end ShielddSecurity.RuntimeTransferAssetNonzero\n'
    return _signature_audits(source)


def complete_assignment(rho):
    """Concrete finite-field replay of the local four-write constructor.

    Missing mapping entries denote zero for replay purposes. This is not a
    full Transfer witness constructor and makes no claim about unselected rows.
    """
    if not isinstance(rho, dict):
        raise relation.RelationError('local asset completion requires a finite assignment mapping')
    for column, value in rho.items():
        relation.natural(column, 262144)
        relation.natural(value, P)
    if rho.get(0, 0) != 1 or rho.get(ASSET, 0) == 0:
        raise relation.RelationError('local asset completion requires constant one and nonzero asset')
    completed = dict(rho)
    inverse = pow(rho[ASSET], -1, P)
    completed.update({INVERSE: inverse, PRODUCT: 1,
                      AUXILIARY: (inverse - rho[ASSET]) ** 2 % P, CONSTANT_COPY: 1})
    return completed


def omission_controls(extracted):
    """Finite-field replay controls for these rows, never a full-circuit test."""
    rows = _validate(extracted)

    def rejected(rho):
        def evaluate(terms):
            return sum(rho[column] * int(encoded, 16) for column, encoded in terms) % P
        return [row['row'] for row in rows
                if evaluate(row['a']) ** 2 % P != evaluate(row['b'])]

    def assignment(asset, inverse, product, auxiliary, copy=1):
        return {0: 1, ASSET: asset, INVERSE: inverse, PRODUCT: product,
                AUXILIARY: auxiliary, CONSTANT_COPY: copy}

    positives = []
    for asset in (1, 17):
        inverse = pow(asset, -1, P)
        rho = assignment(asset, inverse, 1, (inverse - asset) ** 2 % P)
        failures = rejected(rho)
        if failures:
            raise relation.RelationError('asset-nonzero positive selected-row replay failed')
        positives.append(dict(asset=asset, assignment=sorted(rho.items()), rejected_rows=failures))

    # Each zero-asset assignment satisfies precisely the other three rows.
    cases = [
        ('product-minus', ROW_INDICES[0], assignment(0, 0, 1, P - 4)),
        ('product-plus', ROW_INDICES[1], assignment(0, 0, 1, 0)),
        ('product-assertion', ROW_INDICES[2], assignment(0, 0, 0, 0)),
        ('constant-link', ROW_INDICES[3], assignment(0, 0, 0, 0, copy=0)),
    ]
    controls = []
    for name, omitted, rho in cases:
        failures = rejected(rho)
        if failures != [omitted] or rho[ASSET] != 0 or rho[0] != 1:
            raise relation.RelationError('intended zero-asset row omission not observed')
        controls.append(dict(name=name, omitted_row=omitted, original_rejected_rows=failures,
                             remaining_selected_rows_satisfied=True, asset_is_zero=True,
                             assignment=sorted(rho.items())))
    completion = []
    for asset in (1, 17, P - 1):
        before = {0: 1, 1: 37, 2: 41, 6: asset, 73: 43,
                  INVERSE: 123, PRODUCT: 456, AUXILIARY: 789, CONSTANT_COPY: 321}
        after = complete_assignment(before)
        failures = rejected(after)
        if failures or any(after[c] != v for c, v in before.items() if c not in COMPLETION_WRITES):
            raise relation.RelationError('local asset completion/preservation replay failed')
        completion.append(dict(input_assignment=sorted(before.items()),
                               completed_assignment=sorted(after.items()), rejected_rows=failures))
    return dict(scope=SCOPE, selected_rows=list(ROW_INDICES), positive=positives,
                zero_asset_omissions=controls,
                constructive_completion=dict(writes=list(COMPLETION_WRITES), cases=completion,
                    scope='local four-row completion only; other Transfer rows may change'))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    inputs = parser.add_mutually_exclusive_group(required=True)
    inputs.add_argument('--relation', type=Path)
    inputs.add_argument('--extracted', type=Path)
    parser.add_argument('--expected-extraction-sha256')
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    if args.output_dir.exists():
        parser.error('output directory must be fresh; preserve predecessor packets')
    if args.extracted is not None:
        extraction_bytes = args.extracted.read_bytes()
        extracted = from_extraction_bytes(extraction_bytes, args.expected_extraction_sha256)
        input_identity = dict(kind='retained extraction; prior whole-stream receipt required',
                              path=str(args.extracted), sha256=hashlib.sha256(extraction_bytes).hexdigest())
    else:
        if args.expected_extraction_sha256 is not None:
            parser.error('expected extraction SHA256 requires --extracted')
        with args.relation.open('rb') as stream:
            extracted = inspect(stream)
        input_identity = dict(kind='full ordinary stream inspected', path=str(args.relation),
                              sha256=extracted['identity']['raw_sha256'])
    source = generate(extracted)
    controls = omission_controls(extracted)
    root = Path(__file__).resolve().parents[1]
    dependencies = [root / 'circuits/ShielddSecurity/Compiler.lean',
                    root / 'circuits/ShielddSecurity/Rows.lean',
                    root / 'circuits/ShielddSecurity/Arithmetic.lean']
    manifest = dict(schema='shieldd-transfer-asset-nonzero-candidate-v1',
                    scope=SCOPE, qualification='diagnostic candidate; Lean unrun; T0-T7 open',
                    relation_digest=RELATION_DIGEST, raw_relation_sha256=RAW_SHA256,
                    generated_module='ShielddSecurity.RuntimeTransferAssetNonzero',
                    generated_sha256=hashlib.sha256(source.encode()).hexdigest(),
                    named_exports=list(EXPORTS),
                    generation_input=input_identity,
                    completion_scope='local four-row completion only; other Transfer rows may change',
                    completion_writes=list(COMPLETION_WRITES),
                    source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                    dependency_scope='direct and immediate owned imports; root must qualify full transitive closure',
                    dependency_sources=[dict(path=str(path), sha256=hashlib.sha256(path.read_bytes()).hexdigest())
                                        for path in dependencies])
    args.output_dir.mkdir(parents=True, exist_ok=False)
    outputs = {'extracted.json': extracted, 'controls.json': controls, 'manifest.json': manifest}
    for filename, payload in outputs.items():
        with (args.output_dir / filename).open('x', encoding='utf-8', newline='\n') as output:
            json.dump(payload, output, sort_keys=True, indent=2)
            output.write('\n')
    with (args.output_dir / 'RuntimeTransferAssetNonzero.lean').open('x', encoding='utf-8', newline='\n') as output:
        output.write(source)
    print(json.dumps(dict(packet=str(args.output_dir), exports=list(EXPORTS),
                          generated_sha256=manifest['generated_sha256'], scope=SCOPE)))


if __name__ == '__main__':
    main()
