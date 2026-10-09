"""Expose Boolean values and canonical readers from actual coordinate pages."""
from .transfer_encryption_address_rows import SCHEMA


def generate(extraction):
    assert extraction['schema'] == SCHEMA
    result = {}
    for item in extraction['plan']['decompositions']:
        role = item['role']
        assert len(item['plan']['columns']) == len(item['plan']['steps']) == 255
        prefix = 'RuntimeEncryptionAddress' + role + 'Canonical'
        join = prefix + 'Join'
        pages = [prefix + f'Page{i:02}' for i in range(16)]
        name = 'RuntimeEncryptionAddress' + role + 'BitValues'
        text = ('import ShielddSecurity.' + join + '\n'
                'import ShielddSecurity.GroupScalarCodec\n'
                'set_option maxHeartbeats 2000000\n'
                'set_option maxRecDepth 4096\n'
                f'namespace ShielddSecurity.{name}\n'
                f'abbrev bits : List Linear := {join}.bits\n'
                'def bitPages : List (List Linear) := [' + ','.join(
                    page + '.steps.map ScalarRows.StepData.left' for page in pages) + ']\n'
                'variable {F : Type} [Field F] [CharP F Scalar.modulus]\n')
        for i, page in enumerate(pages):
            text += f'''private theorem page{i:02}_values (rho : Nat → F)
    (satisfied : Satisfies rho {join}.rawRows) :
    ∀ bit ∈ {page}.steps.map ScalarRows.StepData.left,
      eval rho bit = if ScalarBits.decodeBit rho bit then 1 else 0 := by
  have own : Satisfies rho {page}.rawRows := by
    intro row member
    apply satisfied row
    change row ∈ {join}.rawPages.flatten ++ {join}.tailRows
    apply List.mem_append_left
    apply List.mem_flatten.mpr
    refine ⟨{page}.rawRows, ?_, member⟩
    simp only [{join}.rawPages, List.mem_cons, List.mem_singleton]
    tauto
  intro bit member
  exact ScalarBits.checked_bit_value rho {page}.expectedRows
    ({page}.rows_sound rho own) ({page}.steps.map ScalarRows.StepData.left)
    {page}.bits_checked bit member
'''
        text += f'''theorem bit_value (rho : Nat → F)
    (satisfied : Satisfies rho {join}.rawRows) (bit : Linear) (member : bit ∈ bits) :
    eval rho bit = if ScalarBits.decodeBit rho bit then 1 else 0 := by
  have shape : bits = bitPages.flatten := by decide
  rw [shape] at member
  obtain ⟨page, pageMember, bitMember⟩ := List.mem_flatten.mp member
  have alternatives : ''' + ' ∨ '.join(
            f'page = {page}.steps.map ScalarRows.StepData.left' for page in pages) + ''' := by
    simpa only [bitPages, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] using pageMember
  rcases alternatives with ''' + ' | '.join(f'p{i:02}' for i in range(16)) + '\n'
        for i in range(16):
            text += f'  · rw [p{i:02}] at bitMember\n    exact page{i:02}_values rho satisfied bit bitMember\n'
        text += f'''theorem bits_value (rho : Nat → F)
    (satisfied : Satisfies rho {join}.rawRows) :
    eval rho (ScalarBits.bitLinear bits) = (binary (ScalarBits.decodeBits rho bits) : F) := by
  classical
  have values : bits.map (eval rho) =
      (ScalarBits.decodeBits rho bits).map (fun bit => if bit then (1 : F) else 0) := by
    simp only [ScalarBits.decodeBits, List.map_map]
    apply List.map_congr_left
    intro bit member
    exact bit_value rho satisfied bit member
  rw [ScalarBits.eval_bitLinear, values, binary_cast]

theorem native_bits (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho {join}.rawRows)
    (native : Nat) (bounded : native < Scalar.modulus)
    (reader : (native : F) = eval rho {join}.output) :
    GroupScalarCodec.readBits 255 native = ScalarBits.decodeBits rho bits := by
  have width : bits.length = 255 := by decide
  apply GroupScalarCodec.binary_injective_same_width
  · simp only [GroupScalarCodec.reader_length, ScalarBits.decodeBits, List.length_map, width]
  · rw [GroupScalarCodec.reader_value 255 native
      (lt_trans bounded GroupScalarCodec.circuit_field_width)]
    exact ({join}.native_integer rho one four satisfied native bounded reader).symm
'''
        for export in ['bit_value', 'bits_value', 'native_bits']:
            text += f'set_option pp.all true in\n#check @{export}\n#print axioms {export}\n'
        text += f'end ShielddSecurity.{name}\n'
        result[name] = text
    assert len(result) == 8
    return result
