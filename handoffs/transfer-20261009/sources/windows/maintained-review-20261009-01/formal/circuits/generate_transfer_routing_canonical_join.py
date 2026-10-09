"""Compose finite physical pages into the full canonical routing integer."""
from .generate_transfer_routing_zero_rows import _lc, _row


def _member(index):
    proof = 'List.mem_cons.mpr (Or.inl rfl)'
    for _ in range(index):
        proof = 'List.mem_cons.mpr (Or.inr (' + proof + '))'
    return proof


def generate(extraction):
    assert extraction['schema'] == 'shieldd-transfer-routing-row-derivative-v1'
    plan = extraction['plan']['permutation']
    assert len(plan['steps']) == len(plan['columns']) == 255
    names = [f'RuntimeRoutingCanonicalPage{i:02}' for i in range(16)]
    name = 'RuntimeRoutingCanonicalJoin'
    raw = {row['row']: row for row in extraction['selected_rows']}
    indices = [plan['reconstruction_row'], plan['final_boolean_row'],
               plan['endpoint_row'], extraction['plan']['constant_link']]
    source = ''.join(f'import ShielddSecurity.{page}\n' for page in names)
    source += ('import ShielddSecurity.RuntimeRoutingChainTheory\n'
               'import ShielddSecurity.RuntimeRoutingCanonicalTheory\n'
               'set_option maxHeartbeats 2000000\nset_option maxRecDepth 4096\n'
               f'namespace ShielddSecurity.{name}\n')
    for label, field in [('rawPages', 'rawRows'), ('expectedPages', 'expectedRows')]:
        source += f'def {label} : List (List Row) := [' + ','.join(page+'.'+field for page in names) + ']\n'
    source += 'def tailIndices : List Nat := ' + str(indices) + '\n'
    source += 'def tailRows : List Row := [' + ','.join(_row(raw[i]['a'], raw[i]['b']) for i in indices) + ']\n'
    source += 'def rawRows : List Row := rawPages.flatten ++ tailRows\n'
    source += 'def steps : List ScalarRows.StepData := ' + ' ++ '.join(page+'.steps' for page in names) + '\n'
    source += 'def output : Linear := ' + _lc(plan['output']) + '\n'
    source += 'def bits : List Linear := [' + ','.join(_lc([[column, 1]]) for column in plan['columns']) + ']\n'
    source += 'def tailExpected : List Row := [⟨Compiler.subtract (ScalarBits.bitLinear bits) output,[]⟩,\n'
    source += f'  ⟨Compiler.subtract {names[-1]}.final [(0,1)],[]⟩]\n'
    source += 'def expectedRows : List Row := expectedPages.flatten ++ tailExpected\n'
    source += '''variable {F : Type} [Field F] [CharP F Scalar.modulus]
private theorem rows_sound (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    Satisfies rho expectedRows := by
  intro row member
  rcases List.mem_append.mp member with inPages | inTail
  · rcases List.mem_flatten.mp inPages with ⟨part,present,belongs⟩
    simp only [expectedPages,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with ''' + ' | '.join('rfl' for _ in names) + '\n'
    for index, page in enumerate(names):
        source += f'''    · apply {page}.rows_sound rho _ row belongs
      intro original owned
      apply satisfied original
      apply List.mem_append_left
      apply List.mem_flatten.mpr
      exact ⟨{page}.rawRows,{_member(index)},owned⟩
'''
    source += '''  · have localRows : Satisfies rho tailRows := by
      intro original owned
      exact satisfied original (List.mem_append_right _ owned)
    have actual := Compiler.unoutline_rows_sound rho 200692 tailRows localRows (by decide)
    exact RowOrientationSoundness.checked_rows rho (Compiler.unoutlineRows 200692 tailRows)
      tailExpected (by decide) actual row inTail
'''
    # Each page is transported symbolically into the common normalized row set.
    for index, page in enumerate(names):
        source += f'''private theorem included{index:02} : ∀ row ∈ {page}.expectedRows, row ∈ expectedRows := by
  intro row member
  apply List.mem_append_left
  apply List.mem_flatten.mpr
  exact ⟨{page}.expectedRows,{_member(index)},member⟩
'''
    source += 'private theorem chain_checked : ScalarRows.checkChain Scalar.modulus expectedRows [(0,1)] steps = true := by\n'
    for index, page in enumerate(names):
        source += f'''  have c{index:02} := RuntimeRoutingChainTheory.chain_monotone Scalar.modulus
    {page}.expectedRows expectedRows included{index:02} {page}.initial {page}.steps {page}.chain_checked
'''
    source += f'  have suffix15 := c15\n'
    for index in range(14, -1, -1):
        page, nextpage = names[index:index+2]
        tail = ' ++ '.join(p+'.steps' for p in names[index+1:])
        source += f'''  have adjacent{index:02} : {page}.final = {nextpage}.initial := by decide
  have suffix{index:02} := RuntimeRoutingChainTheory.chain_append Scalar.modulus expectedRows
    {page}.initial {page}.steps ({tail}) c{index:02}
    (by rw [{page}.endpoint_checked,adjacent{index:02}]; exact suffix{index+1:02})
'''
    source += '  exact suffix00\n'
    source += 'private theorem bits_checked : ScalarBits.checkBits Scalar.modulus expectedRows (steps.map ScalarRows.StepData.left) = true := by\n'
    for index, page in enumerate(names):
        source += f'''  have b{index:02} := RuntimeRoutingChainTheory.bits_monotone Scalar.modulus
    {page}.expectedRows expectedRows included{index:02} ({page}.steps.map ScalarRows.StepData.left) {page}.bits_checked
'''
    source += '  have suffix15 := b15\n'
    for index in range(14, -1, -1):
        page = names[index]
        tail = ' ++ '.join('('+p+'.steps.map ScalarRows.StepData.left)' for p in names[index+1:])
        source += f'''  have suffix{index:02} := RuntimeRoutingChainTheory.bits_append Scalar.modulus expectedRows
    ({page}.steps.map ScalarRows.StepData.left) ({tail}) b{index:02} suffix{index+1:02}
'''
    source += '  simpa only [steps,List.map_append] using suffix00\n'
    source += '''private theorem endpoint_checked : ScalarComparisonBounds.endpoint [(0,1)] steps = RuntimeRoutingCanonicalPage15.final := by
  unfold steps
  simp only [RuntimeRoutingChainTheory.endpoint_append]
'''
    for index, page in enumerate(names):
        # The expression is already reassociated by symbolic endpoint_append.
        source += f'  rw [{page}.endpoint_checked]\n'
        if index < 15:
            source += f'  have adjacent{index:02} : {page}.final = {names[index+1]}.initial := by decide\n'
            source += f'  rw [adjacent{index:02}]\n'
    source += '''private theorem bit_shape : steps.map ScalarRows.StepData.left = bits := by decide
private theorem ending_checked : ScalarComparisonBounds.checkEquality Scalar.modulus expectedRows
    (ScalarComparisonBounds.endpoint [(0,1)] steps) [(0,1)] = true := by
  rw [endpoint_checked]
  apply Bool.or_eq_true.mpr
  apply Or.inl
  exact RuntimeRoutingChainTheory.row_monotone Scalar.modulus tailExpected expectedRows
    (fun row member => List.mem_append_right _ member) _ (by decide)
private theorem reconstruction_checked : ScalarComparisonBounds.checkEquality Scalar.modulus expectedRows
    (ScalarBits.bitLinear (steps.map ScalarRows.StepData.left)) output = true := by
  rw [bit_shape]
  apply Bool.or_eq_true.mpr
  apply Or.inl
  exact RuntimeRoutingChainTheory.row_monotone Scalar.modulus tailExpected expectedRows
    (fun row member => List.mem_append_right _ member) _ (by decide)
theorem canonical_sound (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    let decoded := binary (ScalarBits.decodeBits rho bits)
    decoded < Scalar.modulus ∧ (decoded : F) = eval rho output := by
  have certified := RuntimeRoutingCanonicalTheory.canonical_sound rho expectedRows steps output
    one four (rows_sound rho satisfied) bits_checked chain_checked ending_checked
    reconstruction_checked (by decide) (by decide)
  simpa only [bit_shape] using certified
theorem native_integer (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) (native : Nat) (nativeBound : native < Scalar.modulus)
    (reader : (native : F) = eval rho output) :
    binary (ScalarBits.decodeBits rho bits) = native := by
  have canonical := canonical_sound rho one four satisfied
  exact RuntimeRoutingCanonicalTheory.native_integer _ native (eval rho output)
    canonical.1 nativeBound canonical.2 reader
'''
    for export in ['canonical_sound', 'native_integer']:
        source += f'set_option pp.all true in\n#check @{export}\n#print axioms {export}\n'
    return {name: source + f'end ShielddSecurity.{name}\n'}
