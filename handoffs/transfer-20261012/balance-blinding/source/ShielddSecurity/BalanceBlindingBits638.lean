import ShielddSecurity.HeaderRegisteredConstruction310
import ShielddSecurity.SharedWordLimbMeaning321
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceBlindingBits638
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open RegisteredConstructorFrame309 HeaderRegisteredConstruction310

theorem scalar_bound (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) : w.blinding<TransferCore.scalarOrder :=
  HeaderRegistrySeed299.legal_blinding c w legal

theorem blinding_number (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) : numbers original c w 9=w.blinding := by
  have same := prepared_outside original c w 9 (by decide) (by constructor <;> decide)
  have header := (HeaderRegistrySeed299.original_headers original c w).2.2.2.2.2.2.2.2.2.1
  have bound := lt_trans (scalar_bound c w legal) HeaderRegistrySeed299.scalar_below_field
  exact (congrArg representation.value (same.trans header)).trans
    (RegistryNaturalSeed298.represented_nat _ bound)

def sourceWord : WordHints210.Slot × Nat :=
  (CapturedWordSlots211B016.W65.slot,CapturedWordSlots211B016.W65.first)

theorem source_member : sourceWord∈CapturedWordRoot213.words := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem bits (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w)
    (index : Nat) (before : index<252) :
    completed original c w initial (22232+index)=
      if (encodeBits 252 w.blinding)[index]?.getD false then 1 else 0 := by
  have limb := SharedWordLimbMeaning321.encoded_point
    (CapturedFourSubgroupSeed89.seeded (prepared original c w) initial)
    (LegalWordNormalization272.normalized (numbers original c w))
    (fallback original c w) (LegalWordNormalization272.coherent _)
    sourceWord source_member index before
  have fixed : LegalWordNormalization272.normalized (numbers original c w) 9=w.blinding :=
    (LegalWordNormalization272.fixed _ 9 (by decide)).trans (blinding_number original c w legal)
  change completed original c w initial (22232+index)=
    (if (encodeBits 252 (LegalWordNormalization272.normalized (numbers original c w) 9))[index]?.getD false then 1 else 0) at limb
  simpa only [fixed] using limb
end ShielddSecurity.BalanceBlindingBits638

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingBits638.scalar_bound
#print axioms ShielddSecurity.BalanceBlindingBits638.scalar_bound

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingBits638.blinding_number
#print axioms ShielddSecurity.BalanceBlindingBits638.blinding_number

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingBits638.sourceWord
#print axioms ShielddSecurity.BalanceBlindingBits638.sourceWord

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingBits638.source_member
#print axioms ShielddSecurity.BalanceBlindingBits638.source_member

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingBits638.bits
#print axioms ShielddSecurity.BalanceBlindingBits638.bits
