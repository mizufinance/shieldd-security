import ShielddSecurity.RuntimeBalanceBlindingTemplateCanonicalPreservation
import ShielddSecurity.PoseidonCompletion

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferBalanceBlindingTemplateFrame

def prefixProgram (n : Nat) : GroupFixedCircuitCompletion.Program :=
  RuntimeBalanceBlindingWindow000TemplatePrefix.program
    ((encodeBits 252 n)[0]?.getD false) ((encodeBits 252 n)[1]?.getD false)

def programs (n : Nat) : List GroupFixedCircuitCompletion.Program :=
  prefixProgram n :: (RuntimeBalanceBlindingTemplateOrdinaryTrace.windows n).map
    GroupFixedTemplateTrace.Window.program

/-- The bit block, comparator products, folded prefix and ordinary windows
are exactly the successive writes of the maintained constructor. -/
def ownedWrites (n : Nat) : List Nat :=
  (List.range' 22232 252 ++
    PoseidonCompletion.writes RuntimeBalanceBlindingCanonicalOrder.allStages) ++
  (programs n).flatMap (fun program =>
    program.stages.flatMap GroupCircuitCompletion.Step.writes)

theorem outside_column {F : Type} [Field F] (rho : Nat → F) (n column : Nat)
    (outside : column ∉ ownedWrites n) :
    RuntimeBalanceBlindingTemplateCanonicalPreservation.construct rho n column =
      rho column := by
  have absentBits : column ∉ List.range' 22232 252 := by
    intro member
    exact outside (List.mem_append_left _ (List.mem_append_left _ member))
  have absentProducts : column ∉
      PoseidonCompletion.writes RuntimeBalanceBlindingCanonicalOrder.allStages := by
    intro member
    exact outside (List.mem_append_left _ (List.mem_append_right _ member))
  have protection : ∀ program ∈ programs n,
      GroupFixedCircuitCompletion.Protected [column] program := by
    intro program member stage present current kept written
    have same : current = column := List.mem_singleton.mp kept
    subst current
    exact outside (List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨program, member, List.mem_flatMap.mpr ⟨stage, present, written⟩⟩))
  have loops := GroupFixedCircuitCompletion.run_preserves
    (RuntimeBalanceBlindingCanonicalCompletion.construct rho n)
    (programs n) [column] protection column (List.mem_singleton_self column)
  have products := PoseidonCompletion.run_outside
    (writeBits rho 22232 (encodeBits 252 n))
    RuntimeBalanceBlindingCanonicalOrder.allStages column absentProducts
  have rangeOutside : column < 22232 ∨ 22484 ≤ column := by
    by_contra denied
    have inside : 22232 ≤ column ∧ column < 22232 + 252 := by omega
    exact absentBits (List.mem_range'_1.mpr inside)
  have bits := writeBits_preserves rho 22232 (encodeBits 252 n) column
    (by simpa only [encodeBits_length] using rangeOutside)
  exact loops.trans (products.trans bits)

theorem outside_eval {F : Type} [Field F] (rho : Nat → F) (n : Nat)
    (terms : Linear) (outside : ∀ term ∈ terms, term.1 ∉ ownedWrites n) :
    eval (RuntimeBalanceBlindingTemplateCanonicalPreservation.construct rho n) terms =
      eval rho terms := by
  apply eval_agrees
  intro term member
  exact outside_column rho n term.1 (outside term member)

theorem preserves_rows {F : Type} [Field F] (rho : Nat → F) (n : Nat)
    (prior : List Row)
    (outside : ∀ row ∈ prior, ∀ term ∈ row.a ++ row.b, term.1 ∉ ownedWrites n)
    (initial : Satisfies rho prior) :
    Satisfies (RuntimeBalanceBlindingTemplateCanonicalPreservation.construct rho n) prior := by
  intro row member
  change Square
    (eval (RuntimeBalanceBlindingTemplateCanonicalPreservation.construct rho n) row.a)
    (eval (RuntimeBalanceBlindingTemplateCanonicalPreservation.construct rho n) row.b)
  rw [outside_eval rho n row.a (by
        intro term present
        exact outside row member term (List.mem_append_left _ present)),
      outside_eval rho n row.b (by
        intro term present
        exact outside row member term (List.mem_append_right _ present))]
  exact initial row member

set_option pp.all true in
#check @outside_column
#print axioms outside_column
set_option pp.all true in
#check @outside_eval
#print axioms outside_eval
set_option pp.all true in
#check @preserves_rows
#print axioms preserves_rows

end ShielddSecurity.TransferBalanceBlindingTemplateFrame
