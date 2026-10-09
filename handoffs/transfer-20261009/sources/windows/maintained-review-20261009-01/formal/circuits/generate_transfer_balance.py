"""Generate a diagnostic selected-row certificate, never a promoted receipt."""
import json
from .transfer_balance_rows import inspect, canonical, P


def generate(metadata_bytes, stream, expected_relation):
    checked = inspect(metadata_bytes, stream, expected_relation)
    metadata = json.loads(metadata_bytes)
    raw = {row['row']: row for row in checked['selected_rows']}
    roles = {role: item['row'] for item in checked['templates'] for role in item['roles']}
    expressions = {tuple(item['source']): tuple((column, int(value, 16)) for column, value in item['terms'])
                   for item in metadata['expressions']}
    def linear(terms):
        return '[' + ', '.join(f'({column}, {value})' for column, value in terms) + ']'
    def row(value):
        return '⟨'+linear((i,int(v,16)) for i,v in value['a'])+', '+linear((i,int(v,16)) for i,v in value['b'])+'⟩'
    handles = metadata['handles']
    columns = [handles[i]['values'][0][1]+3 for i in range(4)]
    neg, mag = handles[4]['values'][1][1]+3, handles[4]['values'][2][1]+3
    if len(checked['products']) != 1:
        raise ValueError('current balance certificate requires one selected materialized product')
    product = checked['products'][0]
    node = next(node for node in metadata['nodes'] if node['index']==product['node'])
    a,b = expressions[tuple(node['left'])],expressions[tuple(node['right'])]
    expected_a, expected_b = ((neg,1),),((mag,P-2),)
    if (a,b) not in [(expected_a,expected_b),(expected_b,expected_a)]:
        raise ValueError('current selected product must be negative times minus-two magnitude')
    output = expressions[(2,product['node'])]
    auxiliary = tuple((i,int(v,16)) for i,v in raw[product['rows'][0]]['b'])
    if len(output)!=1 or output[0][1]!=1 or len(auxiliary)!=1 or auxiliary[0][1]!=1:
        raise ValueError('current product/auxiliary must use explicit unit columns')
    out, aux = output[0][0], auxiliary[0][0]
    if expressions[tuple(handles[4]['values'][3])] != canonical([(mag,1),(out,1)]):
        raise ValueError('selected sign expression LC is not magnitude plus observed product')
    namespace = 'ShielddSecurity.RuntimeTransferBalance'
    text = ['import ShielddSecurity.TransferBalanceRows', 'set_option maxHeartbeats 800000',
            'set_option maxRecDepth 4096', f'namespace {namespace}',
            'open ShielddSecurity ShielddSecurity.Compiler ShielddSecurity.TransferCore ShielddSecurity.TransferBalance ShielddSecurity.TransferBalanceRows',
            '/- Diagnostic generated selected-row certificate. Full ordinary-row membership and source-handle extraction are separate joins; no key/setup qualification. -/',
            f'def relationDigest : String := "{expected_relation}"',
            f'def metadataDigest : String := "{checked["metadata_sha256"]}"']
    for i in range(5):
        bits = [bit[1]+3 for bit in handles[i]['bits']]
        indexes = [roles[f'range{i}.boolean{j}'] for j in range(len(bits))]
        recon = roles[f'range{i}.reconstruction']
        value = columns[i] if i<4 else mag
        bound = 'amountBound' if i<4 else '2 * amountBound'
        text += [f'def range{i}Indices : List Nat := {indexes+[recon]}',
                 f'def range{i}Bits : List Nat := {bits}',
                 f'def range{i}Booleans : List Row := ['+',\n'.join(row(raw[index]) for index in indexes)+']',
                 f'def range{i}Reconstruction : Row := {row(raw[recon])}',
                 f'def range{i}Rows : List Row := range{i}Booleans ++ [range{i}Reconstruction]',
                 f'''theorem range{i}_sound {{F : Type}} [Field F] [CharP F fieldModulus]
    (rho : Nat → F) (satisfied : Satisfies rho range{i}Rows) :
    ∃ n : Nat, n < {bound} ∧ (n : F) = rho {value} := by
  have result := selected_range_sound rho range{i}Booleans range{i}Reconstruction
    [({value},1)] range{i}Bits (by decide) (by decide) satisfied
  simpa [range{i}Bits, amountBound, eval, Nat.pow_succ, Nat.mul_comm] using result''']
    indexes = [roles['negative.boolean'],roles['signed.equation'],roles['constant-copy'],*product['rows']]
    text += [f'def signedIndices : List Nat := {indexes}',
             'def signedRows : List Row := ['+',\n'.join(row(raw[index]) for index in indexes)+']',
             'def blocks : List (List Row) := [range0Rows, range1Rows, range2Rows, range3Rows, range4Rows, signedRows]',
             'def selectedRows : List Row := blocks.flatten',
             f'''theorem signed_field_sound {{F : Type}} [Field F] [CharP F fieldModulus]
    (rho : Nat → F) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho signedRows) :
    (rho {neg} = 0 ∨ rho {neg} = 1) ∧
    rho {columns[0]} + rho {columns[1]} - rho {columns[2]} - rho {columns[3]} =
      rho {mag} - 2 * rho {neg} * rho {mag} := by
  have sign := checked_row_sound rho signedRows (booleanRow {neg}) satisfied (by decide)
  have product := checked_product_sound rho signedRows [({neg},1)] [({mag},-2)]
    [({out},1)] [({aux},1)] four satisfied (by decide) (by decide)
  have equation := checked_assertion_sound rho signedRows
    [({columns[0]},1),({columns[1]},1),({columns[2]},-1),({columns[3]},-1)]
    [({mag},1),({out},1)] satisfied (by decide)
  constructor
  · exact boolean_sound _ (by simpa [booleanRow, eval] using sign)
  · have eq : rho {columns[0]} + rho {columns[1]} - rho {columns[2]} - rho {columns[3]} = rho {mag} + rho {out} := by
      simpa [eval, sub_eq_add_neg, add_assoc] using equation
    rw [eq]
    simp only [eval, Int.cast_neg, Int.cast_one, Int.cast_ofNat, one_mul, mul_one, add_zero] at product
    rw [product]
    ring''',
             f'''theorem selected_integer_balance {{F : Type}} [Field F] [CharP F fieldModulus]
    (rho : Nat → F) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho selectedRows) :
    ∃ in0 in1 out0 out1 magnitude : Nat, ∃ negative : Bool,
      in0 < amountBound ∧ in1 < amountBound ∧ out0 < amountBound ∧ out1 < amountBound ∧
      magnitude < 2 * amountBound ∧
      (in0 : F) = rho {columns[0]} ∧ (in1 : F) = rho {columns[1]} ∧
      (out0 : F) = rho {columns[2]} ∧ (out1 : F) = rho {columns[3]} ∧
      (magnitude : F) = rho {mag} ∧ rho {neg} = (if negative then 1 else 0) ∧
      (in0 : Int) + (in1 : Int) - (out0 : Int) - (out1 : Int) =
        if negative then -(magnitude : Int) else (magnitude : Int) := by
  have block (rows : List Row) (present : rows ∈ blocks) : Satisfies rho rows :=
    satisfies_block blocks rows present rho satisfied
  obtain ⟨in0, h0⟩ := range0_sound rho (block _ (by simp [blocks]))
  obtain ⟨in1, h1⟩ := range1_sound rho (block _ (by simp [blocks]))
  obtain ⟨out0, h2⟩ := range2_sound rho (block _ (by simp [blocks]))
  obtain ⟨out1, h3⟩ := range3_sound rho (block _ (by simp [blocks]))
  obtain ⟨magnitude, hm⟩ := range4_sound rho (block _ (by simp [blocks]))
  obtain ⟨sign, equation⟩ := signed_field_sound rho four (block _ (by simp [blocks]))
  obtain ⟨negative, signValue⟩ : ∃ negative : Bool, rho {neg} = (if negative then 1 else 0) := by
    rcases sign with sign | sign
    · exact ⟨false, by simpa using sign⟩
    · exact ⟨true, by simpa using sign⟩
  have fieldEquation : (in0 : F) + (in1 : F) - (out0 : F) - (out1 : F) =
      if negative then -(magnitude : F) else (magnitude : F) := by
    rw [h0.2, h1.2, h2.2, h3.2, hm.2]
    cases negative with
    | false => simpa [signValue] using equation
    | true =>
      simp only [↓reduceIte] at signValue ⊢
      rw [signValue] at equation
      calc
        _ = rho {mag} - 2 * 1 * rho {mag} := equation
        _ = -rho {mag} := by ring
  exact ⟨in0, in1, out0, out1, magnitude, negative, h0.1, h1.1, h2.1, h3.1, hm.1,
    h0.2, h1.2, h2.2, h3.2, hm.2, signValue,
    signed_magnitude_sound in0 in1 out0 out1 magnitude negative h0.1 h1.1 h2.1 h3.1 hm.1 fieldEquation⟩''']
    for name in [*(f'range{i}_sound' for i in range(5)), 'signed_field_sound','selected_integer_balance']:
        text += ['set_option pp.all true in',f'#check @{name}',f'#print axioms {name}']
    text += [f'end {namespace}']
    return '\n\n'.join(text)+'\n', checked


def generate_semantic_composition(balance_metadata_bytes, canonical_metadata_bytes,
                                  stream, expected_relation):
    """Generate a real selected-row-to-independent-balance-domain composition.

    The caller must separately instantiate the five explicit source-role links
    and canonical decoded-value preconditions. This never asserts all TransferSem
    conjuncts or promotes full-relation membership/source extraction.
    """
    from .transfer_canonical_balance import inspect as inspect_canonical
    # One full framing/hash pass for each source-bound selected-row inventory.
    checked = inspect(balance_metadata_bytes, stream, expected_relation)
    stream.seek(0)
    canonical_checked = inspect_canonical(canonical_metadata_bytes, stream, expected_relation)
    metadata = json.loads(balance_metadata_bytes)
    columns = [metadata['handles'][i]['values'][0][1] + 3 for i in range(4)]
    source = f"""import ShielddSecurity.RuntimeTransferBalance
import ShielddSecurity.RuntimeTransferCanonicalBalance
import ShielddSecurity.TransferSem

set_option maxHeartbeats 400000
namespace ShielddSecurity.RuntimeTransferArithmeticSem
open ShielddSecurity ShielddSecurity.TransferCore ShielddSecurity.TransferSem
open ShielddSecurity.Compiler

/-- Arbitrary assignments satisfying the two extracted actual-row slices yield
independent semantic balance-input bounds for the linked canonical decoded
values. The five links are explicit source-refinement prerequisites. This does
not establish other TransferSem components or full ordinary-row membership. -/
theorem actual_rows_balance_domain {{F : Type}} [Field F] [CharP F fieldModulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (balanceRows : Satisfies rho RuntimeTransferBalance.selectedRows)
    (canonicalRows : Satisfies rho RuntimeTransferCanonicalBalance.originalRows)
    (in0 in1 out0 out1 blinding : Nat)
    (decoded : in0 < fieldModulus ∧ in1 < fieldModulus ∧
      out0 < fieldModulus ∧ out1 < fieldModulus ∧ blinding < fieldModulus)
    (links : (in0 : F) = rho {columns[0]} ∧ (in1 : F) = rho {columns[1]} ∧
      (out0 : F) = rho {columns[2]} ∧ (out1 : F) = rho {columns[3]} ∧
      (blinding : F) = rho 2) :
    BalanceInputsSem in0 in1 out0 out1 blinding := by
  obtain ⟨a, b, x, y, magnitude, negative, ha, hb, hx, hy, hm,
      ea, eb, ex, ey, em, en, net⟩ :=
    RuntimeTransferBalance.selected_integer_balance rho four balanceRows
  obtain ⟨blind, hblind, eblind⟩ :=
    RuntimeTransferCanonicalBalance.committed_canonical rho one four canonicalRows
  have capacity : amountBound < fieldModulus := by decide
  have scalarCapacity : scalarOrder < fieldModulus := by decide
  have equalA : in0 = a := bounded_cast_injective decoded.1
    (lt_trans ha capacity) (links.1.trans ea.symm)
  have equalB : in1 = b := bounded_cast_injective decoded.2.1
    (lt_trans hb capacity) (links.2.1.trans eb.symm)
  have equalX : out0 = x := bounded_cast_injective decoded.2.2.1
    (lt_trans hx capacity) (links.2.2.1.trans ex.symm)
  have equalY : out1 = y := bounded_cast_injective decoded.2.2.2.1
    (lt_trans hy capacity) (links.2.2.2.1.trans ey.symm)
  have equalBlind : blinding = blind := bounded_cast_injective decoded.2.2.2.2
    (lt_trans hblind scalarCapacity) (links.2.2.2.2.trans eblind.symm)
  exact ⟨equalA.symm ▸ ha, equalB.symm ▸ hb, equalX.symm ▸ hx,
    equalY.symm ▸ hy, equalBlind.symm ▸ hblind⟩

set_option pp.all true in
#check @actual_rows_balance_domain
#print axioms actual_rows_balance_domain
end ShielddSecurity.RuntimeTransferArithmeticSem
"""
    return source, {'balance': checked, 'canonical': canonical_checked,
                    'scope': 'selected-row balance domain; source links remain explicit'}
