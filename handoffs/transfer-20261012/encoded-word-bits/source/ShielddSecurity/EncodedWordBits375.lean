import ShielddSecurity.EncodedWordConstruction374
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.EncodedWordBits375
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def value (w : TransferSem.Witness) (column : Nat) : Nat :=
  if column∈AuthScalarSeed366.values then AuthScalarSeed366.value w column else RemainingWordSeed369.value w column

def width (column : Nat) : Nat :=
  if column∈AuthScalarSeed366.values then AuthScalarSeed366.width column else RemainingWordSeed369.width column

def base (original : Nat → F) (w : TransferSem.Witness)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  UserSubgroupSeed352.seed (UserPathSeed361.seed
    (AuthScalarSeed366.seed (RemainingWordSeed369.seed original w) w) w) w senderInitial receiverInitial

theorem value_bound (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem (crypto c) w)
    (column : Nat) (inside : SemanticWordFrame373.Inside column) : value w column<2^width column := by
  by_cases auth : column∈AuthScalarSeed366.values
  · rw [value,width,if_pos auth,if_pos auth]
    exact AuthScalarSeed366.value_bound c w legal column auth
  · have remaining : column∈RemainingWordSeed369.values := (List.mem_append.mp inside).resolve_left auth
    rw [value,width,if_neg auth,if_neg auth]
    exact RemainingWordSeed369.value_bound c w legal column remaining

theorem width_below_field (column : Nat) : 2^width column<TransferCore.fieldModulus := by
  unfold width
  split
  · exact AuthScalarSeed366.width_below_field column
  · exact RemainingWordSeed369.width_below_field column

theorem final_value (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (column : Nat) (inside : SemanticWordFrame373.Inside column) :
    SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial column=(value w column:F) := by
  by_cases auth : column∈AuthScalarSeed366.values
  · rw [value,if_pos auth]
    exact SemanticWordFrame373.auth_value original c w initial senderInitial receiverInitial column auth
  · rw [value,if_neg auth]
    exact SemanticWordFrame373.remaining_value original c w initial senderInitial receiverInitial column
      ((List.mem_append.mp inside).resolve_left auth)

theorem prepared_number (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (legal : TransferSem.TransferSem (crypto c) w) (column : Nat) (inside : SemanticWordFrame373.Inside column) :
    HeaderRegisteredConstruction310.numbers (UserLifecycleWord345.originalBase (base original w senderInitial receiverInitial) w) c w column=value w column := by
  have limits := SemanticWordFrame373.limits column inside
  have same := SemanticWordFrame373.completed_outside
    (CapturedFourSubgroupSeed89.seeded (RegisteredConstructorFrame309.prepared
      (UserLifecycleWord345.originalBase (base original w senderInitial receiverInitial) w) c w) initial)
    (LegalWordNormalization272.normalized (HeaderRegisteredConstruction310.numbers
      (UserLifecycleWord345.originalBase (base original w senderInitial receiverInitial) w) c w))
    (HeaderRegisteredConstruction310.fallback (UserLifecycleWord345.originalBase
      (base original w senderInitial receiverInitial) w) c w) column inside
  change SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial column=
    CapturedFourSubgroupSeed89.seeded (RegisteredConstructorFrame309.prepared
      (UserLifecycleWord345.originalBase (base original w senderInitial receiverInitial) w) c w) initial column at same
  rw [CapturedFourSubgroupSeed89.seeded_outside _ initial column (by
    simp only [CapturedFourSubgroupSeed89.hintColumns,List.mem_cons,List.not_mem_nil,or_false];omega),
    final_value original c w initial senderInitial receiverInitial column inside] at same
  change representation.value (RegisteredConstructorFrame309.prepared
    (UserLifecycleWord345.originalBase (base original w senderInitial receiverInitial) w) c w column)=_
  rw [←same,RegistryNaturalSeed298.represented_nat _
    (lt_trans (value_bound c w legal column inside) (width_below_field column))]

theorem aliases_checked : SemanticWordFrame373.values.all (fun column =>
    decide (¬LegalWordNormalization272.Alias column)) = true := by decide +kernel

theorem selected_bits (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (legal : TransferSem.TransferSem (crypto c) w) (entry : WordHints210.Slot × Nat)
    (member : entry∈CapturedWordRoot213.words) (inside : SemanticWordFrame373.Inside entry.1.value) :
    ∀ index<entry.1.width,
      SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial (entry.1.start+index)=
      BooleanHints207.bitValue ((encodeBits entry.1.width (value w entry.1.value))[index]?.getD false) := by
  intro index bound
  let source := UserLifecycleWord345.originalBase (base original w senderInitial receiverInitial) w
  have point := SharedWordLimbMeaning321.encoded_point
    (CapturedFourSubgroupSeed89.seeded (RegisteredConstructorFrame309.prepared source c w) initial)
    (LegalWordNormalization272.normalized (HeaderRegisteredConstruction310.numbers source c w))
    (HeaderRegisteredConstruction310.fallback source c w) (LegalWordNormalization272.coherent _) entry member index bound
  have outside := of_decide_eq_true (List.all_eq_true.mp aliases_checked entry.1.value inside)
  have fixed := (LegalWordNormalization272.fixed (HeaderRegisteredConstruction310.numbers source c w)
    entry.1.value outside).trans (prepared_number original c w initial senderInitial receiverInitial legal entry.1.value inside)
  change SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial (entry.1.start+index)=_ at point
  rw [fixed] at point
  exact point

end ShielddSecurity.EncodedWordBits375

set_option pp.all true in
#check @ShielddSecurity.EncodedWordBits375.value
#print axioms ShielddSecurity.EncodedWordBits375.value

set_option pp.all true in
#check @ShielddSecurity.EncodedWordBits375.width
#print axioms ShielddSecurity.EncodedWordBits375.width

set_option pp.all true in
#check @ShielddSecurity.EncodedWordBits375.base
#print axioms ShielddSecurity.EncodedWordBits375.base

set_option pp.all true in
#check @ShielddSecurity.EncodedWordBits375.value_bound
#print axioms ShielddSecurity.EncodedWordBits375.value_bound

set_option pp.all true in
#check @ShielddSecurity.EncodedWordBits375.width_below_field
#print axioms ShielddSecurity.EncodedWordBits375.width_below_field

set_option pp.all true in
#check @ShielddSecurity.EncodedWordBits375.final_value
#print axioms ShielddSecurity.EncodedWordBits375.final_value

set_option pp.all true in
#check @ShielddSecurity.EncodedWordBits375.prepared_number
#print axioms ShielddSecurity.EncodedWordBits375.prepared_number

set_option pp.all true in
#check @ShielddSecurity.EncodedWordBits375.aliases_checked
#print axioms ShielddSecurity.EncodedWordBits375.aliases_checked

set_option pp.all true in
#check @ShielddSecurity.EncodedWordBits375.selected_bits
#print axioms ShielddSecurity.EncodedWordBits375.selected_bits
