import ShielddSecurity.TransferScalarPowInvariant01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarInvertMachine01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarPowInvariant01 (sourceRepeatedSquare sourceCanonicalMul)
/-! A small symbolic register machine represents the source inversion
addition chain. Uninitialized reads refuse evaluation; square counts use
the symbolic repeated-square recurrence and multiply uses the actual proved
word model. Initialized source reads imply successful execution and retain
canonical register fields. The exact parsed source instruction list and
zero Choice projection are separate instances of this machine. -/

inductive InvertOperand where
  | input
  | register (index : Nat)

inductive InvertInstruction where
  | square (target : Nat) (source : InvertOperand) (count : Nat)
  | multiply (target : Nat) (left right : InvertOperand)

def RegisterState := Nat → Option CanonicalScalar

def registerInitialized (state : RegisterState) (defined : List Nat) : Prop :=
  ∀ index, index ∈ defined → ∃ value, state index = some value

def operandInitialized (defined : List Nat) : InvertOperand → Prop
  | .input => True
  | .register index => index ∈ defined

def sourceOperand (self : CanonicalScalar) (state : RegisterState) : InvertOperand → Option CanonicalScalar
  | .input => some self
  | .register index => state index

def sourceRegisterPut (state : RegisterState) (target : Nat) (value : CanonicalScalar) : RegisterState :=
  fun index => if index = target then some value else state index

def instructionTarget : InvertInstruction → Nat
  | .square target _ _ => target
  | .multiply target _ _ => target

def instructionReadsInitialized (defined : List Nat) : InvertInstruction → Prop
  | .square _ source _ => operandInitialized defined source
  | .multiply _ left right => operandInitialized defined left ∧ operandInitialized defined right

def sourceApply (self : CanonicalScalar) (state : RegisterState) : InvertInstruction → Option RegisterState
  | .square target source count => do
    let value ← sourceOperand self state source
    return sourceRegisterPut state target (sourceRepeatedSquare count value)
  | .multiply target left right => do
    let l ← sourceOperand self state left
    let r ← sourceOperand self state right
    return sourceRegisterPut state target (sourceCanonicalMul l r)

def sourceWalk (self : CanonicalScalar) : List InvertInstruction → RegisterState → Option RegisterState
  | [], state => some state
  | instruction :: rest, state => do
    let updated ← sourceApply self state instruction
    sourceWalk self rest updated

def sourceAssigned : List Nat → List InvertInstruction → List Nat
  | defined, [] => defined
  | defined, instruction :: rest => sourceAssigned (instructionTarget instruction :: defined) rest

def sourceWellFormed : List Nat → List InvertInstruction → Prop
  | _, [] => True
  | defined, instruction :: rest => instructionReadsInitialized defined instruction ∧
      sourceWellFormed (instructionTarget instruction :: defined) rest

def sourceExponentOperand (state : Nat → Option Nat) : InvertOperand → Option Nat
  | .input => some 1
  | .register index => state index

def sourceExponentApply (state : Nat → Option Nat) : InvertInstruction → Option (Nat → Option Nat)
  | .square target source count => do
    let value ← sourceExponentOperand state source
    return fun index => if index = target then some (value * 2 ^ count) else state index
  | .multiply target left right => do
    let l ← sourceExponentOperand state left
    let r ← sourceExponentOperand state right
    return fun index => if index = target then some (l + r) else state index

def sourceExponentWalk : (Nat → Option Nat) → List InvertInstruction → Option (Nat → Option Nat)
  | state, [] => some state
  | state, instruction :: rest => do
    let updated ← sourceExponentApply state instruction
    sourceExponentWalk updated rest

theorem initialized_operand_has_exact_successful_source_read
    (self : CanonicalScalar) (state : RegisterState) (defined : List Nat) (operand : InvertOperand)
    (initialized : registerInitialized state defined) (good : operandInitialized defined operand) :
    ∃ value, sourceOperand self state operand = some value := by
  cases operand with
  | input => exact ⟨self, rfl⟩
  | register index => exact initialized index good

theorem source_register_put_preserves_all_initialized_reads
    (state : RegisterState) (defined : List Nat) (target : Nat) (value : CanonicalScalar)
    (initialized : registerInitialized state defined) :
    registerInitialized (sourceRegisterPut state target value) (target :: defined) := by
  intro index inside
  by_cases same : index = target
  · exact ⟨value, by simp only [sourceRegisterPut, if_pos same]⟩
  · have old : index ∈ defined := (List.mem_cons.mp inside).resolve_left same
    obtain ⟨prior, returned⟩ := initialized index old
    exact ⟨prior, by simp only [sourceRegisterPut, if_neg same, returned]⟩

theorem initialized_instruction_derives_successful_updated_registers
    (self : CanonicalScalar) (state : RegisterState) (defined : List Nat) (instruction : InvertInstruction)
    (initialized : registerInitialized state defined) (good : instructionReadsInitialized defined instruction) :
    ∃ updated, sourceApply self state instruction = some updated ∧
      registerInitialized updated (instructionTarget instruction :: defined) := by
  cases instruction with
  | square target source count =>
    obtain ⟨value, returned⟩ := initialized_operand_has_exact_successful_source_read self state defined source initialized good
    refine ⟨sourceRegisterPut state target (sourceRepeatedSquare count value), ?_,
      source_register_put_preserves_all_initialized_reads state defined target _ initialized⟩
    change (sourceOperand self state source).bind (fun v => some (sourceRegisterPut state target (sourceRepeatedSquare count v))) = _
    rw [returned] <;> rfl
  | multiply target left right =>
    obtain ⟨l, leftRead⟩ := initialized_operand_has_exact_successful_source_read self state defined left initialized good.1
    obtain ⟨r, rightRead⟩ := initialized_operand_has_exact_successful_source_read self state defined right initialized good.2
    refine ⟨sourceRegisterPut state target (sourceCanonicalMul l r), ?_,
      source_register_put_preserves_all_initialized_reads state defined target _ initialized⟩
    change (sourceOperand self state left).bind (fun l => (sourceOperand self state right).bind
      (fun r => some (sourceRegisterPut state target (sourceCanonicalMul l r)))) = _
    rw [leftRead]
    change (sourceOperand self state right).bind (fun r => some (sourceRegisterPut state target (sourceCanonicalMul l r))) = _
    rw [rightRead] <;> rfl

theorem well_formed_symbolic_inversion_walk_derives_successful_initialized_result
    (self : CanonicalScalar) (instructions : List InvertInstruction) (state : RegisterState) (defined : List Nat)
    (initialized : registerInitialized state defined) (good : sourceWellFormed defined instructions) :
    ∃ result, sourceWalk self instructions state = some result ∧
      registerInitialized result (sourceAssigned defined instructions) := by
  induction instructions generalizing state defined with
  | nil => exact ⟨state, rfl, initialized⟩
  | cons instruction rest ih =>
    obtain ⟨updated, returned, updatedInitialized⟩ :=
      initialized_instruction_derives_successful_updated_registers self state defined instruction initialized good.1
    obtain ⟨result, walked, resultInitialized⟩ := ih updated (instructionTarget instruction :: defined) updatedInitialized good.2
    refine ⟨result, ?_, resultInitialized⟩
    change (sourceApply self state instruction).bind (fun updated => sourceWalk self rest updated) = some result
    rw [returned]
    exact walked

set_option pp.all true in
#check @InvertOperand
#print axioms InvertOperand
set_option pp.all true in
#check @InvertInstruction
#print axioms InvertInstruction
set_option pp.all true in
#check @RegisterState
#print axioms RegisterState
set_option pp.all true in
#check @registerInitialized
#print axioms registerInitialized
set_option pp.all true in
#check @operandInitialized
#print axioms operandInitialized
set_option pp.all true in
#check @sourceOperand
#print axioms sourceOperand
set_option pp.all true in
#check @sourceRegisterPut
#print axioms sourceRegisterPut
set_option pp.all true in
#check @instructionTarget
#print axioms instructionTarget
set_option pp.all true in
#check @instructionReadsInitialized
#print axioms instructionReadsInitialized
set_option pp.all true in
#check @sourceApply
#print axioms sourceApply
set_option pp.all true in
#check @sourceWalk
#print axioms sourceWalk
set_option pp.all true in
#check @sourceAssigned
#print axioms sourceAssigned
set_option pp.all true in
#check @sourceWellFormed
#print axioms sourceWellFormed
set_option pp.all true in
#check @sourceExponentOperand
#print axioms sourceExponentOperand
set_option pp.all true in
#check @sourceExponentApply
#print axioms sourceExponentApply
set_option pp.all true in
#check @sourceExponentWalk
#print axioms sourceExponentWalk
set_option pp.all true in
#check @initialized_operand_has_exact_successful_source_read
#print axioms initialized_operand_has_exact_successful_source_read
set_option pp.all true in
#check @source_register_put_preserves_all_initialized_reads
#print axioms source_register_put_preserves_all_initialized_reads
set_option pp.all true in
#check @initialized_instruction_derives_successful_updated_registers
#print axioms initialized_instruction_derives_successful_updated_registers
set_option pp.all true in
#check @well_formed_symbolic_inversion_walk_derives_successful_initialized_result
#print axioms well_formed_symbolic_inversion_walk_derives_successful_initialized_result
end ShielddSecurity.TransferScalarInvertMachine01
