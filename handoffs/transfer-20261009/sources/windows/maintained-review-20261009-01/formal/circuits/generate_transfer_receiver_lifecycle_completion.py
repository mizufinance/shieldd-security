"""Compose bounded receiver range and nine gate pages with allocation frames."""
from . import transfer_relation as relation
from .generate_hash_round import _signature_audits


def generate(floors):
    if (not isinstance(floors, list) or len(floors) != 9 or
            any(type(value) is not int or not 1980 < value < 200692 for value in floors) or
            floors != sorted(set(floors))):
        raise relation.RelationError('nine captured increasing receiver allocation floors required')
    pages = [f'TransferReceiverLifecycleGatePageCompletion{i:02}' for i in range(9)]
    name = 'TransferReceiverLifecycleCompletion'
    text = 'import ShielddSecurity.RuntimeTransferReceiverLifecycleRange\n'
    text += 'import ShielddSecurity.ScalarWrittenBitValues\n'
    text += ''.join(f'import ShielddSecurity.{page}\n' for page in pages)
    text += f'''namespace ShielddSecurity.{name}
set_option maxHeartbeats 300000

def stepBlocks : List (List CompilerCompletion.Step) := [{','.join(page+'.steps' for page in pages)}]
def steps : List CompilerCompletion.Step := stepBlocks.flatten
def gateBlocks : List (List Row) := [{','.join(page+'.rows' for page in pages)}]
def blocks : List (List Row) := RuntimeTransferReceiverLifecycleRange.rawRows :: gateBlocks
def rows : List Row := blocks.flatten
def writes : List Nat := List.range' 1849 131 ++ PoseidonCompletion.writes steps
def encoded {{F : Type}} [Field F] (base : Nat → F) (n : Nat) : Nat → F :=
  RuntimeTransferReceiverLifecycleRange.completeAssignment base n
def completed {{F : Type}} [Field F] (base : Nat → F) (n : Nat) : Nat → F :=
  CompilerCompletion.run (encoded base n) steps

theorem preserved {{F : Type}} [Field F] (base : Nat → F) (n column : Nat)
    (outside : column ∉ writes) : completed base n column = base column := by
  have split : column ∉ List.range' 1849 131 ∧ column ∉ PoseidonCompletion.writes steps := by
    simpa only [writes,List.mem_append,not_or] using outside
  have interval : column < 1849 ∨ 1849+131 ≤ column := by
    by_contra bad
    have bounds : 1849 ≤ column ∧ column < 1849+131 := by omega
    exact split.1 (List.mem_range'.mpr ⟨column-1849,by omega,by simp only [Nat.one_mul]; omega⟩)
  exact (PoseidonCompletion.run_outside (encoded base n) steps column split.2).trans
    (writeBits_preserves base 1849 (encodeBits 131 n) column (by simpa only [encodeBits_length] using interval))

theorem complete {{F : Type}} [Field F] [CharP F Scalar.modulus]
    (base : Nat → F) (one : base 0 = 1) (linked : base 200692 = base 0)
    (n : Nat) (bound : n < 2^131) (meaning : base 1767 = (n : F))
    (flag : Bool) (flagMeaning : base 10 = if flag then 1 else 0)
    (legal : flag = true → ReceiverLifecycle.LegalActive n) :
    Satisfies (completed base n) rows := by
  have initial := RuntimeTransferReceiverLifecycleRange.complete_actual_range base n bound meaning linked
  have fixed (column : Nat) (outside : column < 1849 ∨ 1849+131 ≤ column) : encoded base n column = base column :=
    writeBits_preserves base 1849 (encodeBits 131 n) column (by simpa only [encodeBits_length] using outside)
  have written (i : Nat) (inside : i < 131) : encoded base n (1849+i) =
      if (encodeBits 131 n)[i]?.getD false then 1 else 0 :=
    ScalarWrittenBitValues.field_bit_value base 1849 (encodeBits 131 n) i
      (by simpa only [encodeBits_length] using inside)
  intro row member
  obtain ⟨part,present,member⟩ := List.mem_flatten.mp member
  simp only [blocks,gateBlocks,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with {' | '.join('rfl' for _ in range(10))}
  · have outside := CompilerSequenceCompletion.frame_rows 200692 {floors[0]} []
      (PoseidonCompletion.writes steps) RuntimeTransferReceiverLifecycleRange.rawRows
      (by decide) (by decide)
    exact CompilerSequenceCompletion.preserves_rows (encoded base n) steps
      RuntimeTransferReceiverLifecycleRange.rawRows initial.1 outside row member
'''
    for k, page in enumerate(pages):
        prefix_program = '['+','.join(p+'.steps' for p in pages[:k])+']'
        suffix = '['+','.join(p+'.steps' for p in pages[k+1:])+']'
        text += f'''  · let prefixProgram : List CompilerCompletion.Step := ({prefix_program} : List (List CompilerCompletion.Step)).flatten
    let suffix : List CompilerCompletion.Step := ({suffix} : List (List CompilerCompletion.Step)).flatten
    let before : Nat → F := CompilerCompletion.run (encoded base n) prefixProgram
    have input (column : Nat) (outside : column ∉ PoseidonCompletion.writes prefixProgram) : before column = encoded base n column :=
      PoseidonCompletion.run_outside (encoded base n) prefixProgram column outside
    have unit : before 0 = 1 := (input 0 (by decide)).trans ((fixed 0 (by omega)).trans one)
    have copy : before 200692 = before 0 := by
      rw [input 200692 (by decide),input 0 (by decide),fixed 200692 (by omega),fixed 0 (by omega),linked]
    have flagValue : before 10 = if flag then 1 else 0 :=
      (input 10 (by decide)).trans ((fixed 10 (by omega)).trans flagMeaning)
    have bits : ∀ i ∈ {page}.indices,before (1849+i) = if (encodeBits 131 n)[i]?.getD false then 1 else 0 := by
      intro i present
      have bounds : i < 131 := by
        have certificate : {page}.indices.all (fun i => decide (i < 131)) = true := by decide
        exact of_decide_eq_true (List.all_eq_true.mp certificate i present)
      have outside : 1849+i ∉ PoseidonCompletion.writes prefixProgram := by
        apply CompilerSequenceCompletion.frame_column 200692 {floors[0]} []
        · decide
        · simp only [List.not_mem_nil,not_false_eq_true,and_true]
          exact Or.inr (by omega)
      exact (input (1849+i) outside).trans (written i bounds)
    have built := {page}.complete before unit copy n flag flagValue bits legal
    have splitSteps : steps = prefixProgram ++ {page}.steps ++ suffix := rfl
    have assignment : completed base n = CompilerCompletion.run ({page}.completed before) suffix := by
      change CompilerCompletion.run (encoded base n) steps = _
      rw [splitSteps,CompilerSequenceCompletion.run_append,CompilerSequenceCompletion.run_append]
      rfl
'''
        if k < 8:
            text += f'''    have outside := CompilerSequenceCompletion.frame_rows 200692 {floors[k+1]} []
      (PoseidonCompletion.writes suffix) {page}.rows (by decide) (by decide)
'''
        else:
            text += f'''    have outside : ∀ actual ∈ {page}.rows,∀ term ∈ actual.a ++ actual.b,
        term.1 ∉ PoseidonCompletion.writes suffix := by simp [suffix,PoseidonCompletion.writes]
'''
        text += f'''    have retained := CompilerSequenceCompletion.preserves_rows ({page}.completed before) suffix {page}.rows built outside
    rw [assignment]
    exact retained row member
'''
    text += f'''#print axioms preserved
#print axioms complete
end ShielddSecurity.{name}
'''
    return name, _signature_audits(text)
