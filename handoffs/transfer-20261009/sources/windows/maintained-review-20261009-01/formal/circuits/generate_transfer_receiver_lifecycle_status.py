"""Compose checked physical receiver gates on the same reconstructed word."""
from .generate_hash_round import _signature_audits
from . import transfer_relation as relation

INDICES = (0, 1, 2, *range(67, 131))


def generate_page(page):
    page = relation.natural(page, 9)
    indices = INDICES[page * 8:(page + 1) * 8]
    name = f'TransferReceiverLifecycleStatusPage{page:02}'
    gates = [f'RuntimeTransferReceiverLifecycleGate{i:03}' for i in indices]
    values = [f'TransferReceiverLifecycleGateValue{i:03}' for i in indices]
    text = ''.join(f'import ShielddSecurity.{dep}\n' for dep in (*gates, *values))
    text += f'''namespace ShielddSecurity.{name}
set_option maxHeartbeats 200000

def indices : List Nat := {list(indices)}
def blocks : List (List Row) := [{','.join(gate + '.rawRows' for gate in gates)}]
def rows : List Row := blocks.flatten

theorem values {{F : Type}} [Field F] [CharP F Scalar.modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (enabled : rho 10 = 1) (satisfied : Satisfies rho rows) :
    ∀ i ∈ indices,rho (1849 + i) = if i = 0 then 1 else 0 := by
  intro i member
  simp only [indices,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with {' | '.join('rfl' for _ in indices)}
'''
    for gate, value in zip(gates, values):
        text += f'''  · apply {value}.value rho one four enabled
    intro row member
    exact satisfied row (List.mem_flatten.mpr ⟨{gate}.rawRows,by simp [blocks],member⟩)
'''
    text += f'''#print axioms values
end ShielddSecurity.{name}
'''
    return name, _signature_audits(text)


def generate_join():
    name = 'TransferReceiverLifecycleStatusSoundness'
    pages = [f'TransferReceiverLifecycleStatusPage{i:02}' for i in range(9)]
    text = 'import ShielddSecurity.TransferReceiverLifecycleWord\n'
    text += 'import ShielddSecurity.ReceiverLifecycleFieldStatus\n'
    text += ''.join(f'import ShielddSecurity.{page}\n' for page in pages)
    text += f'''namespace ShielddSecurity.{name}
set_option maxHeartbeats 250000

def indexBlocks : List (List Nat) := [{','.join(page + '.indices' for page in pages)}]
def indices : List Nat := indexBlocks.flatten
def gateBlocks : List (List Row) := [{','.join(page + '.rows' for page in pages)}]
def blocks : List (List Row) := RuntimeTransferReceiverLifecycleRange.rawRows :: gateBlocks
def rows : List Row := blocks.flatten

private theorem block_rows {{F : Type}} [Field F] (rho : Nat → F)
    (satisfied : Satisfies rho rows) (block : List Row) (inside : block ∈ blocks) :
    Satisfies rho block := by
  intro row member
  exact satisfied row (List.mem_flatten.mpr ⟨block,inside,member⟩)

private theorem constraints {{F : Type}} [Field F] [CharP F Scalar.modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (enabled : rho 10 = 1) (satisfied : Satisfies rho rows) :
    ∀ i ∈ indices,rho (1849 + i) = if i = 0 then 1 else 0 := by
  intro i member
  obtain ⟨page,present,member⟩ := List.mem_flatten.mp member
  simp only [indexBlocks,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with {' | '.join('rfl' for _ in pages)}
'''
    for page in pages:
        text += f'''  · exact {page}.values rho one four enabled
      (block_rows rho satisfied {page}.rows (by simp [blocks,gateBlocks])) i member
'''
    text += '''
theorem sound {F : Type} [Field F] [CharP F Scalar.modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (enabled : rho 10 = 1) (satisfied : Satisfies rho rows) :
    ∃ n : Nat,n < 2^131 ∧ (n : F) = rho 1767 ∧ ReceiverLifecycle.LegalActive n := by
  have rangeRows := block_rows rho satisfied RuntimeTransferReceiverLifecycleRange.rawRows
    (by simp [blocks])
  obtain ⟨n,bound,meaning,word⟩ := TransferReceiverLifecycleWord.word rho rangeRows
  have width : (encodeBits 131 n).length = 131 := encodeBits_length 131 n
  have columnWidth : RuntimeTransferReceiverLifecycleRange.bits.length = (encodeBits 131 n).length := by
    rw [width];decide
  have columnsLength : RuntimeTransferReceiverLifecycleRange.bits.length = 131 := by decide
  have actualColumn : ∀ i,(inside : i < 131) → RuntimeTransferReceiverLifecycleRange.bits[i]'(by omega) = 1849 + i := by
    intro i inside
    have layout : RuntimeTransferReceiverLifecycleRange.bits = List.range' 1849 131 := by decide
    simp only [layout,List.getElem_range']
  have bitMeaning : ∀ i,(inside : i < 131) → rho (1849 + i) =
      if (encodeBits 131 n)[i]'(by omega) then 1 else 0 := by
    intro i inside
    have projected := ReceiverLifecycleFieldStatus.mapped_value rho RuntimeTransferReceiverLifecycleRange.bits
      (encodeBits 131 n) columnWidth word i (by omega)
    simpa only [actualColumn i inside] using projected
  have constrained := constraints rho one four enabled satisfied
  have layout : indices = [0,1,2] ++ List.range' 67 64 := by decide
  have low0 : (encodeBits 131 n)[0]'(by omega) = true :=
    ReceiverLifecycleFieldStatus.boolean_injective _ _ ((bitMeaning 0 (by omega)).symm.trans (constrained 0 (by decide)))
  have low1 : (encodeBits 131 n)[1]'(by omega) = false :=
    ReceiverLifecycleFieldStatus.boolean_injective _ _ ((bitMeaning 1 (by omega)).symm.trans (constrained 1 (by decide)))
  have low2 : (encodeBits 131 n)[2]'(by omega) = false :=
    ReceiverLifecycleFieldStatus.boolean_injective _ _ ((bitMeaning 2 (by omega)).symm.trans (constrained 2 (by decide)))
  have high : ∀ i,67 ≤ i → (inside : i < (encodeBits 131 n).length) → (encodeBits 131 n)[i] = false := by
    intro i lower inside
    have small : i < 131 := by simpa only [width] using inside
    have member : i ∈ indices := by
      rw [layout]
      apply List.mem_append_right
      exact List.mem_range'.mpr ⟨lower,by omega⟩
    have value := constrained i member
    have zero : rho (1849 + i) = 0 := by simpa only [if_neg (by omega : i ≠ 0)] using value
    exact ReceiverLifecycleFieldStatus.boolean_injective _ _ ((bitMeaning i small).symm.trans zero)
  have active := ReceiverLifecycleFieldStatus.status_active (encodeBits 131 n) width low0 low1 low2 high
  exact ⟨n,bound,meaning,by simpa only [encodeBits_value 131 n bound] using active⟩

#print axioms sound
end ShielddSecurity.TransferReceiverLifecycleStatusSoundness
'''
    return name, _signature_audits(text)
