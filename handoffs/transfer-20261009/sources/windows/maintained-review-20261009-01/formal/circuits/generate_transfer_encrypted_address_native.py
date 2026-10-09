"""Join same-assignment coordinate bits, physical ciphers and owned byte packing."""
from .generate_hash_round import linear
from .transfer_balance_rows import canonical
from .transfer_encryption_address_rows import SCHEMA


def generate(extraction):
    assert extraction['schema'] == SCHEMA
    decompositions = {item['role']: item['plan'] for item in extraction['plan']['decompositions']}
    result = {}
    for address in extraction['plan']['addresses']:
        owner = address['owner']
        assert owner in ['Receiver', 'Sender']
        roles = [owner + suffix for suffix in ['GeneratorX', 'GeneratorY', 'TransmissionX', 'TransmissionY']]
        assert address['coordinate_roles'] == roles
        plans = [decompositions[role] for role in roles]
        assert all(canonical(plan['output']) == canonical(coordinate)
                   for plan, coordinate in zip(plans, address['coordinates']))
        joins = ['RuntimeEncryptionAddress' + role + 'CanonicalJoin' for role in roles]
        values = ['RuntimeEncryptionAddress' + role + 'BitValues' for role in roles]
        cipher = 'RuntimeEncryptionAddress' + owner + 'CipherRows'
        name = 'RuntimeEncryptionAddress' + owner + 'NativePacking'
        gx, gy, tx, ty = joins
        vx, vy, wx, wy = values
        gp = linear([(plans[0]['columns'][0], 1)])
        tp = linear([(plans[2]['columns'][0], 1)])
        text = ''.join('import ShielddSecurity.' + value + '\n' for value in values)
        text += ('import ShielddSecurity.' + cipher + '\n'
                 'import ShielddSecurity.AddressByteReader\n'
                 'set_option maxHeartbeats 2000000\n'
                 'set_option maxRecDepth 4096\n'
                 f'namespace ShielddSecurity.{name}\n'
                 'def rawRows : List Row := ' + ' ++ '.join(
                     module + '.rawRows' for module in [cipher] + joins) + '\n'
                 f'def generatorParity : Linear := {gp}\n'
                 f'def transmissionParity : Linear := {tp}\n'
                 f'def allBits : List Linear := {vy}.bits ++ ([generatorParity] ++ '
                 f'({wy}.bits ++ [transmissionParity]))\n'
                 'variable {F : Type} [Field F] [CharP F Scalar.modulus]\n')
        for i, module in enumerate([cipher] + joins):
            text += f'''private theorem own{i} (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    Satisfies rho {module}.rawRows := by
  intro row member
  apply satisfied row
  simp only [rawRows, List.mem_append]
  tauto
'''
        text += f'''private theorem bit_truth (rho : Nat → F) (satisfied : Satisfies rho rawRows)
    (bit : Linear) (member : bit ∈ allBits) :
    eval rho bit = if ScalarBits.decodeBit rho bit then 1 else 0 := by
  simp only [allBits, List.mem_append, List.mem_singleton] at member
  rcases member with h | h | h | h
  · exact {vy}.bit_value rho (own2 rho satisfied) bit h
  · subst bit
    exact {vx}.bit_value rho (own1 rho satisfied) generatorParity (by decide)
  · exact {wy}.bit_value rho (own4 rho satisfied) bit h
  · subst bit
    exact {wx}.bit_value rho (own3 rho satisfied) transmissionParity (by decide)

private theorem binary_value (rho : Nat → F) (satisfied : Satisfies rho rawRows)
    (bits : List Linear) (subset : ∀ bit ∈ bits, bit ∈ allBits) :
    eval rho (ScalarBits.bitLinear bits) = (binary (ScalarBits.decodeBits rho bits) : F) := by
  classical
  have values : bits.map (eval rho) = (ScalarBits.decodeBits rho bits).map
      (fun bit => if bit then (1 : F) else 0) := by
    simp only [ScalarBits.decodeBits, List.map_map]
    apply List.map_congr_left
    intro bit member
    exact bit_truth rho satisfied bit (subset bit member)
  rw [ScalarBits.eval_bitLinear, values, binary_cast]

def addressBytes (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (rho : Nat → F) : List AddressBytePacking.Byte :=
  AddressByteReader.addressBytes codec writer (eval rho {gx}.output) (eval rho {gy}.output)
    (eval rho {tx}.output) (eval rho {ty}.output)

theorem address_bits (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    ScalarBits.decodeBits rho allBits = AddressBytePacking.byteBits (addressBytes codec writer rho) := by
  have generatorX := {vx}.native_bits rho one four (own1 rho satisfied)
    (codec.decode (eval rho {gx}.output)) (codec.bounded _) (codec.roundtrip _)
  have generatorY := {vy}.native_bits rho one four (own2 rho satisfied)
    (codec.decode (eval rho {gy}.output)) (codec.bounded _) (codec.roundtrip _)
  have transmissionX := {wx}.native_bits rho one four (own3 rho satisfied)
    (codec.decode (eval rho {tx}.output)) (codec.bounded _) (codec.roundtrip _)
  have transmissionY := {wy}.native_bits rho one four (own4 rho satisfied)
    (codec.decode (eval rho {ty}.output)) (codec.bounded _) (codec.roundtrip _)
  have generatorHead : {vx}.bits = generatorParity :: {vx}.bits.tail := by decide
  have transmissionHead : {wx}.bits = transmissionParity :: {wx}.bits.tail := by decide
  have generatorLow := congrArg (fun bits : List Bool => bits.getD 0 false) generatorX
  have transmissionLow := congrArg (fun bits : List Bool => bits.getD 0 false) transmissionX
  change decide (codec.decode (eval rho {gx}.output) % 2 = 1) =
    (ScalarBits.decodeBits rho {vx}.bits).getD 0 false at generatorLow
  change decide (codec.decode (eval rho {tx}.output) % 2 = 1) =
    (ScalarBits.decodeBits rho {wx}.bits).getD 0 false at transmissionLow
  rw [generatorHead] at generatorLow
  rw [transmissionHead] at transmissionLow
  simp only [ScalarBits.decodeBits, List.map_cons, List.getD_cons_zero] at generatorLow transmissionLow
  rw [addressBytes, AddressByteReader.address_byte_bits]
  simp only [allBits, ScalarBits.decodeBits, List.map_append, List.map_cons, List.map_nil]
  rw [generatorLow, transmissionLow, generatorY, transmissionY]
  simp only [ScalarBits.decodeBits, List.append_assoc]
'''
        for ordinal, start, count in [(0, 0, 31), (1, 31, 31), (2, 62, 2)]:
            word = address['words'][ordinal]
            assert len(word['columns']) == count * 8
            output, stream = linear(canonical(word['output'])), linear(canonical(word['stream']))
            text += f'''theorem cipher{ordinal} (codec : TransferReduction.CanonicalField F)
    (writer : GroupByteCodec.BEWrite codec) {{Raw : Type}}
    (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    eval rho {output} = eval rho {stream} + ShielddNativeScalar.value operations
      (AddressBytePacking.nativeWord operations (((addressBytes codec writer rho).drop {start}).take {count})) := by
  have shape : {cipher}.bits{ordinal} = (allBits.drop {8 * start}).take {8 * count} := by decide
  have subset : ∀ bit ∈ {cipher}.bits{ordinal}, bit ∈ allBits := by
    intro bit member
    rw [shape] at member
    exact List.mem_of_mem_drop (List.mem_of_mem_take member)
  have asserted := {cipher}.cipher{ordinal} rho (own0 rho satisfied)
  rw [{cipher}.word{ordinal} rho, binary_value rho satisfied _ subset] at asserted
  rw [shape] at asserted
  have decoded : ScalarBits.decodeBits rho ((allBits.drop {8 * start}).take {8 * count}) =
      ((ScalarBits.decodeBits rho allBits).drop {8 * start}).take {8 * count} := by
    simp only [ScalarBits.decodeBits, List.map_take, List.map_drop]
  rw [decoded, address_bits codec writer rho one four satisfied] at asserted
  have inside : {start} + {count} ≤ (addressBytes codec writer rho).length := by
    simpa only [addressBytes, AddressByteReader.address_length] using
      (show {start} + {count} ≤ 64 from by decide)
  rw [AddressBytePacking.slice_value operations (addressBytes codec writer rho) {start} {count} inside]
  exact asserted
'''
        for export in ['address_bits', 'cipher0', 'cipher1', 'cipher2']:
            text += f'set_option pp.all true in\n#check @{export}\n#print axioms {export}\n'
        text += f'end ShielddSecurity.{name}\n'
        result[name] = text
    assert len(result) == 2
    return result
