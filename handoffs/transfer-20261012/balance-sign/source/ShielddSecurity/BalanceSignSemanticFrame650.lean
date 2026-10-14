import ShielddSecurity.BalanceSignHeaderFrame649
import ShielddSecurity.AuthorizationSharedFrame420B
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceSignSemanticFrame650
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open BalanceSignLayout647 (columns flags)

def userSeed (original : Nat → F) (w : TransferSem.Witness)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  RegistryComparisonSeed318.seed (HighZeroSeed329.seed (UserWordSeed342.seed
    (UserSubgroupSeed352.seed original w senderInitial receiverInitial) w) w) w

theorem user_seed_outside (original : Nat → F) (w : TransferSem.Witness)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (column : Nat) (member : column∈columns) :
    userSeed original w senderInitial receiverInitial column=original column := by
  have bounds := BalanceSignLayout647.bounds column member
  unfold userSeed
  rw [RegistryComparisonSeed318.seed_outside _ w column (by
    simp only [RegistryComparisonSeed318.written,List.mem_cons,List.not_mem_nil,or_false]; omega),
    HighZeroSeed329.outside _ w column (Or.inr (by omega)) (Or.inr (by omega)),
    UserWordSeed342.seed_outside _ w column (by
      simp only [UserWordSeed342.values,List.mem_cons,List.not_mem_nil,or_false]; omega)]
  exact UserSubgroupSeed352.outside original w senderInitial receiverInitial column (by omega) (by omega)

theorem user_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (column : Nat) (member : column∈columns)
    (boolean : column∈flags → original column=0 ∨ original column=1) :
    UserLifecycleWord345.assignment (UserSubgroupSeed352.seed original w senderInitial receiverInitial)
      c w initial column=original column := by
  have preserved := user_seed_outside original w senderInitial receiverInitial column member
  change HeaderRegisteredConstruction310.completed (userSeed original w senderInitial receiverInitial)
    c w initial column=original column
  exact (BalanceSignHeaderFrame649.completed _ c w initial column member
    (by rw [preserved]; exact boolean)).trans preserved

def semanticSeed (original : Nat → F) (w : TransferSem.Witness) : Nat → F :=
  UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed original w) w) w

theorem semantic_seed_outside (original : Nat → F) (w : TransferSem.Witness)
    (column : Nat) (member : column∈columns) : semanticSeed original w column=original column := by
  have bounds := BalanceSignLayout647.bounds column member
  unfold semanticSeed
  rw [UserPathSeed361.outside _ w column (by omega) (by omega) (by omega) (by omega),
    AuthScalarSeed366.seed_outside _ w column (by
      simp only [AuthScalarSeed366.values,List.mem_cons,List.not_mem_nil,or_false]; omega),
    RemainingWordSeed369.seed_outside original w column (by
      simp only [RemainingWordSeed369.values,List.mem_cons,List.not_mem_nil,or_false]; omega)]

theorem semantic_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (column : Nat) (member : column∈columns)
    (boolean : column∈flags → original column=0 ∨ original column=1) :
    SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial column=original column := by
  have preserved := semantic_seed_outside original w column member
  exact (user_frame (semanticSeed original w) c w initial senderInitial receiverInitial column member
    (by rw [preserved]; exact boolean)).trans preserved

def authorizationSeed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) : Nat → F :=
  AuthorizationPointSeed405.seed (AuthorizationSharedSeed416.seed original c w) w authInitial

theorem authorization_seed_outside (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) (column : Nat) (member : column∈columns) :
    authorizationSeed original c w authInitial column=original column := by
  have bounds := BalanceSignLayout647.bounds column member
  unfold authorizationSeed
  rw [AuthorizationPointSeed405.outside _ w authInitial column (by omega) (by omega)]
  exact AuthorizationSharedSeed416.outside original c w column (by omega)

theorem authorization_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (column : Nat) (member : column∈columns)
    (boolean : column∈flags → original column=0 ∨ original column=1) :
    AuthorizationSharedFrame420B.assignment original c w authInitial initial senderInitial receiverInitial column=original column := by
  have preserved := authorization_seed_outside original c w authInitial column member
  exact (semantic_frame (authorizationSeed original c w authInitial) c w initial senderInitial receiverInitial
    column member (by rw [preserved]; exact boolean)).trans preserved

end ShielddSecurity.BalanceSignSemanticFrame650

set_option pp.all true in
#check @ShielddSecurity.BalanceSignSemanticFrame650.userSeed
#print axioms ShielddSecurity.BalanceSignSemanticFrame650.userSeed

set_option pp.all true in
#check @ShielddSecurity.BalanceSignSemanticFrame650.user_seed_outside
#print axioms ShielddSecurity.BalanceSignSemanticFrame650.user_seed_outside

set_option pp.all true in
#check @ShielddSecurity.BalanceSignSemanticFrame650.user_frame
#print axioms ShielddSecurity.BalanceSignSemanticFrame650.user_frame

set_option pp.all true in
#check @ShielddSecurity.BalanceSignSemanticFrame650.semanticSeed
#print axioms ShielddSecurity.BalanceSignSemanticFrame650.semanticSeed

set_option pp.all true in
#check @ShielddSecurity.BalanceSignSemanticFrame650.semantic_seed_outside
#print axioms ShielddSecurity.BalanceSignSemanticFrame650.semantic_seed_outside

set_option pp.all true in
#check @ShielddSecurity.BalanceSignSemanticFrame650.semantic_frame
#print axioms ShielddSecurity.BalanceSignSemanticFrame650.semantic_frame

set_option pp.all true in
#check @ShielddSecurity.BalanceSignSemanticFrame650.authorizationSeed
#print axioms ShielddSecurity.BalanceSignSemanticFrame650.authorizationSeed

set_option pp.all true in
#check @ShielddSecurity.BalanceSignSemanticFrame650.authorization_seed_outside
#print axioms ShielddSecurity.BalanceSignSemanticFrame650.authorization_seed_outside

set_option pp.all true in
#check @ShielddSecurity.BalanceSignSemanticFrame650.authorization_frame
#print axioms ShielddSecurity.BalanceSignSemanticFrame650.authorization_frame
