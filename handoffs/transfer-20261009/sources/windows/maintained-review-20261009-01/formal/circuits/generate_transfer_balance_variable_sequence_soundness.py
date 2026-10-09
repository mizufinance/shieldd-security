"""Join all genuine balance windows on an arbitrary satisfying assignment."""
from . import generate_transfer_balance_variable_completion as local
from . import transfer_relation as relation
from .generate_hash_round import linear, _signature_audits


def generate(accepted):
    if len(accepted.get('programs', ())) != 65:
        raise relation.RelationError('sound sequence requires the complete genuine65 plan')
    seq = 'RuntimeBalanceVariableSequence'
    name = seq + 'Soundness'
    programs = [local.PREFIX + f'{i:03d}Program' for i in range(65)]
    d = 'RuntimeBalanceVariableWindow000Point0Cones.coefficientD'
    last = accepted['programs'][-1]
    last_page = accepted['checked']['chunks'][last['page_ordinal']]
    if any(value[0] != 'source' for value in last['outgoing']):
        raise relation.RelationError('sound sequence genuine final source coordinates')
    output = [last_page['derived'][value[1]] for value in last['outgoing']]
    source = f'import ShielddSecurity.{seq}\n'
    source += 'import ShielddSecurity.RuntimeBalanceVariableProgramSoundness\n'
    source += 'import ShielddSecurity.RuntimeBalanceVariableTableSoundness\n'
    source += 'import ShielddSecurity.RuntimeTransferSignedBalanceWordSoundness\n'
    source += ''.join(f'import ShielddSecurity.{p}Soundness\n' for p in programs[2:])
    source += f'''namespace ShielddSecurity.{name}
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
def outputX : Linear := {linear(output[0])}
def outputY : Linear := {linear(output[1])}
def outputPoint {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F :=
  ⟨eval rho outputX,eval rho outputY⟩

theorem output_identity {{F : Type}} [Field F] (rho : Nat → F) (n : Nat) :
    GroupFixedCircuitCompletion.point rho
      (GroupFixedCircuitCompletion.output {seq}.input ({seq}.programs n)) = outputPoint rho := rfl

theorem local_formulas {{F : Type}} [Field F] [CharP F Scalar.modulus]
    (n : Nat) (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare ({d} : F)) (imaginarySquare : imaginary * imaginary = -1) :
    ∀ program ∈ {seq}.programs n,
      GroupVariableCircuitSoundness.LocalSound ({d} : F) 200692 {seq}.tables program := by
  intro program member
  simp only [{seq}.programs,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with ''' + ' | '.join('rfl' for _ in programs) + '\n'
    source += '  · exact RuntimeBalanceVariableProgramSoundness.first _ _\n'
    source += '  · exact RuntimeBalanceVariableProgramSoundness.later four imaginary nonSquare imaginarySquare _ _\n'
    source += ''.join(f'  · exact {p}Soundness.local_sound four imaginary nonSquare imaginarySquare _ _\n'
                      for p in programs[2:])
    source += f'''
theorem aligned (n : Nat) : GroupFixedCircuitCompletion.Aligned {seq}.input ({seq}.programs n) := by
  simp only [{seq}.programs,{seq}.input,GroupFixedCircuitCompletion.Aligned,
    {','.join(p+'.program' for p in programs)}]

theorem row_identity (n : Nat) : {seq}.ownedRows n = {seq}.ownedRows 0 := rfl

theorem bit_meanings {{F : Type}} [Field F] (rho : Nat → F) (n : Nat)
    (word : (List.range' 21713 129).map rho = (encodeBits 129 n).map (fun bit => if bit then (1 : F) else 0)) :
    ∀ program ∈ {seq}.programs n,
      eval rho program.low = (if program.lowBit then 1 else 0) ∧
      eval rho program.high = (if program.highBit then 1 else 0) := by
  intro program member
  simp only [{seq}.programs,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with ''' + ' | '.join('rfl' for _ in programs) + '\n'
    for index, item in enumerate(accepted['programs']):
        if item['index'] != index:
            raise relation.RelationError('sound sequence exact ordered original windows')
        page = accepted['checked']['chunks'][item['page_ordinal']]
        def observe(value):
            return page['derived'][value[1]] if value[0] == 'source' else local.completion.canonical([(0, value[1])])
        low, high = map(observe, item['bits'])
        low_index = 128 - 2 * index
        high_index = 129 - 2 * index
        if low != ((21713 + low_index, 1),) or (high != () if index == 0 else high != ((21713 + high_index, 1),)):
            raise relation.RelationError('sound sequence exact reversed129 source pair and native false padding')
        source += f'''  · change eval rho {linear(low)} = _ ∧ eval rho {linear(high)} = _
    simp only [eval,Int.cast_one,one_mul,add_zero,List.map_nil,List.sum_nil]
    constructor
    · exact RuntimeTransferSignedBalanceWordSoundness.bit_value rho n {low_index} (by decide) word
'''
        source += '    · rfl\n' if index == 0 else f'    · exact RuntimeTransferSignedBalanceWordSoundness.bit_value rho n {high_index} (by decide) word\n'
    source += f'''
theorem native_value {{J : Type}} [AddCommGroup J] (base : J) (n : Nat) :
    GroupVariableCircuitNative.nativeValue base ({seq}.programs n) 0 = binary (encodeBits 129 n) • base := by
  have order : GroupVariableCircuitNative.pairs ({seq}.programs n) =
      (GroupNativeMultiply.pairBits (encodeBits 129 n)).reverse := rfl
  unfold GroupVariableCircuitNative.nativeValue
  rw [order]
  exact GroupNativeMultiply.pair_loop_value base (encodeBits 129 n)

/-- All magnitude bits, table products and window equations use this unchanged
assignment. The source/native seed meaning is the remaining asset-map join. -/
theorem actual_scalar {{F J : Type}} [Field F] [AddCommGroup J] [CharP F Scalar.modulus]
    (rho : Nat → F) (one : rho 0 = 1) (linked : rho 200692 = rho 0)
    (four : (4 : F) ≠ 0) (imaginary : F) (nonSquare : Group.NoUnitSquare ({d} : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (model : Group.StandardCurveModel J ({d} : F)) (base : J)
    (baseMeaning : RuntimeBalanceVariableWindow000Point0Completion.inputPoint rho = model.coordinates base)
    (signedRows : Satisfies rho RuntimeTransferSignedBalanceCompletion.rawRows)
    (variableRows : Satisfies rho ({seq}.ownedRows 0)) :
    ∃ n : Nat, n < 2^129 ∧ (n : F) = rho 21712 ∧
      outputPoint rho = model.coordinates (n • base) := by
  obtain ⟨n,bound,value,word⟩ := RuntimeTransferSignedBalanceWordSoundness.canonical_word rho signedRows
  have rows : Satisfies rho ({seq}.ownedRows n) := by
    rw [row_identity]; exact variableRows
  have tableRows : Satisfies rho RuntimeBalanceVariableTableSoundness.rawRows := by
    intro row member
    have same : {seq}.priorRows = RuntimeBalanceVariableTableSoundness.rawRows := by
      simp only [{seq}.priorRows,RuntimeBalanceVariableWindow000NativePrecompute.firstRows,
        RuntimeBalanceVariableTableSoundness.rawRows,RuntimeBalanceVariableWindow000Point0Soundness.rawRows,
        RuntimeBalanceVariableWindow000Point1Soundness.rawRows,List.append_assoc]
    have priorMember : row ∈ {seq}.priorRows := by rw [same]; exact member
    exact rows row (List.mem_append_left _ priorMember)
  have loopRows : Satisfies rho (GroupFixedCircuitCompletion.rows ({seq}.programs n)) := by
    intro row member; exact rows row (List.mem_append_right _ member)
  have tables := RuntimeBalanceVariableTableSoundness.native_tables rho one four imaginary nonSquare
    imaginarySquare model base baseMeaning tableRows
  have incoming : GroupFixedCircuitCompletion.point rho {seq}.input = model.coordinates 0 := by
    rw [model.identity]
    simp only [{seq}.input,GroupFixedCircuitCompletion.point,Group.identityPoint,eval,
      List.map_nil,List.sum_nil,Int.cast_one,one_mul,add_zero,one]
  have result := GroupVariableCircuitSoundness.checked_native ({d} : F) 200692 model base 0 rho
    {seq}.tables ({seq}.programs n) {seq}.input (local_formulas n four imaginary nonSquare imaginarySquare)
    (aligned n) one linked incoming tables.1 tables.2.1 tables.2.2 (bit_meanings rho n word) loopRows
  rw [native_value,encodeBits_value 129 n bound,output_identity] at result
  exact ⟨n,bound,value,result⟩
#print axioms local_formulas
#print axioms output_identity
#print axioms aligned
#print axioms row_identity
#print axioms bit_meanings
#print axioms native_value
#print axioms actual_scalar
end ShielddSecurity.{name}
'''
    return name, _signature_audits(source)
