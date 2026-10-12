import ShielddSecurity.SharedSeedShape265
import ShielddSecurity.RegistryRecovery194
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RegistrySeedFrame265
open CompilerArithmeticTransport41 PoseidonNatural192
abbrev Protected (column : Nat) : Prop := column≠10 ∧ ((3≤column ∧ column<49) ∨ (134≤column ∧ column<184))
theorem outside_seed (column : Nat) (preserved : Protected column) : column∉SharedWordWitness221.seedColumns := by
 intro member
 have shape:=SharedSeedShape265.seed_shape column member
 rcases shape with equal|middle|above <;> rcases preserved with ⟨different,low|high⟩ <;> omega
variable {F : Type} [Field F]
theorem seeded_frame (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
 (column : Nat) (preserved : Protected column) : SharedWordWitness221.seeded base numbers fallback column=base column :=
 BooleanHints207.seeded_outside base _ _ column (outside_seed column preserved)
theorem completed_frame (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
 (column : Nat) (preserved : Protected column) : SharedWordWitness221.completed base numbers fallback column=base column := by
 have bounds : 3≤column ∧ column<22738 := by rcases preserved.2 with low|high <;> omega
 have input:=CapturedFullRelation58.candidate_inputs (SharedWordWitness221.seeded base numbers fallback) (column-3) (by omega)
 have same : 3+(column-3)=column := by omega
 rw [same] at input
 exact input.trans (seeded_frame base numbers fallback column preserved)
theorem recover_frame (representation : CanonicalRepresentation F) (base : Nat → F)
 (numbers : Nat → Nat) (fallback : Nat → Bool) :
 RegistryRecovery194.recover representation (SharedWordWitness221.completed base numbers fallback)=RegistryRecovery194.recover representation base := by
 unfold RegistryRecovery194.recover
 simp only [completed_frame base numbers fallback 11 (by constructor <;> omega),completed_frame base numbers fallback 12 (by constructor <;> omega),completed_frame base numbers fallback 13 (by constructor <;> omega),completed_frame base numbers fallback 14 (by constructor <;> omega),completed_frame base numbers fallback 15 (by constructor <;> omega),completed_frame base numbers fallback 21 (by constructor <;> omega),completed_frame base numbers fallback 22 (by constructor <;> omega),completed_frame base numbers fallback 23 (by constructor <;> omega),completed_frame base numbers fallback 24 (by constructor <;> omega),completed_frame base numbers fallback 30 (by constructor <;> omega),completed_frame base numbers fallback 31 (by constructor <;> omega),completed_frame base numbers fallback 32 (by constructor <;> omega),completed_frame base numbers fallback 33 (by constructor <;> omega),completed_frame base numbers fallback 34 (by constructor <;> omega),completed_frame base numbers fallback 35 (by constructor <;> omega),completed_frame base numbers fallback 36 (by constructor <;> omega),completed_frame base numbers fallback 42 (by constructor <;> omega),completed_frame base numbers fallback 43 (by constructor <;> omega),completed_frame base numbers fallback 135 (by constructor <;> omega)]
 congr 1
 funext level slot
 have a:=level.isLt
 have b:=slot.isLt
 exact congrArg representation.value (completed_frame base numbers fallback (136+3*level.val+slot.val) (by constructor <;> omega))
theorem anchor_frame (representation : CanonicalRepresentation F) (base : Nat → F)
 (numbers : Nat → Nat) (fallback : Nat → Bool) :
 representation.value (SharedWordWitness221.completed base numbers fallback 4)=representation.value (base 4) :=
 congrArg representation.value (completed_frame base numbers fallback 4 (by constructor <;> omega))
end ShielddSecurity.RegistrySeedFrame265

set_option pp.all true in
#check @ShielddSecurity.RegistrySeedFrame265.Protected
#print axioms ShielddSecurity.RegistrySeedFrame265.Protected
set_option pp.all true in
#check @ShielddSecurity.RegistrySeedFrame265.outside_seed
#print axioms ShielddSecurity.RegistrySeedFrame265.outside_seed
set_option pp.all true in
#check @ShielddSecurity.RegistrySeedFrame265.seeded_frame
#print axioms ShielddSecurity.RegistrySeedFrame265.seeded_frame
set_option pp.all true in
#check @ShielddSecurity.RegistrySeedFrame265.completed_frame
#print axioms ShielddSecurity.RegistrySeedFrame265.completed_frame
set_option pp.all true in
#check @ShielddSecurity.RegistrySeedFrame265.recover_frame
#print axioms ShielddSecurity.RegistrySeedFrame265.recover_frame
set_option pp.all true in
#check @ShielddSecurity.RegistrySeedFrame265.anchor_frame
#print axioms ShielddSecurity.RegistrySeedFrame265.anchor_frame
