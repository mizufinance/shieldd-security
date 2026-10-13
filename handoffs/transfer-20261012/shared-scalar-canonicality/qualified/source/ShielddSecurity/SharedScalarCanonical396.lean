import ShielddSecurity.ScalarCanonicalDomain394
import ShielddSecurity.ScalarCanonicalRows395
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedScalarCanonical396
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def valueColumn (family : Fin 9) : Nat := [3766,4930,6334,8551,10083,11611,13629,14891,16153][family.val]!
def sourceWord (family : Fin 9) : WordHints210.Slot × Nat :=
  if family.val=0 then (CapturedWordSlots211B004.W18.slot,CapturedWordSlots211B004.W18.first)
  else if family.val=1 then (CapturedWordSlots211B006.W26.slot,CapturedWordSlots211B006.W26.first)
  else if family.val=2 then (CapturedWordSlots211B007.W28.slot,CapturedWordSlots211B007.W28.first)
  else if family.val=3 then (CapturedWordSlots211B009.W38.slot,CapturedWordSlots211B009.W38.first)
  else if family.val=4 then (CapturedWordSlots211B010.W41.slot,CapturedWordSlots211B010.W41.first)
  else if family.val=5 then (CapturedWordSlots211B011.W44.slot,CapturedWordSlots211B011.W44.first)
  else if family.val=6 then (CapturedWordSlots211B011.W45.slot,CapturedWordSlots211B011.W45.first)
  else if family.val=7 then (CapturedWordSlots211B011.W46.slot,CapturedWordSlots211B011.W46.first)
  else (CapturedWordSlots211B011.W47.slot,CapturedWordSlots211B011.W47.first)

theorem role_checked : (List.finRange 9).all (fun family => decide
    ((sourceWord family).1.value=valueColumn family ∧ (sourceWord family).1.width=252 ∧
     (sourceWord family).1.start=ScalarCanonicalRows395.bitStart family)) = true := by decide +kernel

theorem role (family : Fin 9) :
    (sourceWord family).1.value=valueColumn family ∧ (sourceWord family).1.width=252 ∧
    (sourceWord family).1.start=ScalarCanonicalRows395.bitStart family :=
  of_decide_eq_true (List.all_eq_true.mp role_checked family (List.mem_finRange family))

theorem values_checked : (List.finRange 9).all (fun family => decide
    (valueColumn family∈ScalarCanonicalDomain394.values)) = true := by decide +kernel

theorem value_member (family : Fin 9) : valueColumn family∈ScalarCanonicalDomain394.values :=
  of_decide_eq_true (List.all_eq_true.mp values_checked family (List.mem_finRange family))

theorem word_member (family : Fin 9) : sourceWord family∈CapturedWordRoot213.words := by
  have cases : family.val=0 ∨ family.val=1 ∨ family.val=2 ∨ family.val=3 ∨ family.val=4 ∨ family.val=5 ∨ family.val=6 ∨ family.val=7 ∨ family.val=8 := by omega
  rcases cases with h0|h1|h2|h3|h4|h5|h6|h7|h8
  · have same : family=⟨0,by decide⟩ := Fin.ext h0
    subst family
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))
  · have same : family=⟨1,by decide⟩ := Fin.ext h1
    subst family
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))
  · have same : family=⟨2,by decide⟩ := Fin.ext h2
    subst family
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))
  · have same : family=⟨3,by decide⟩ := Fin.ext h3
    subst family
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))))))
  · have same : family=⟨4,by decide⟩ := Fin.ext h4
    subst family
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))))))))
  · have same : family=⟨5,by decide⟩ := Fin.ext h5
    subst family
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))))))))))))
  · have same : family=⟨6,by decide⟩ := Fin.ext h6
    subst family
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))))))))))))
  · have same : family=⟨7,by decide⟩ := Fin.ext h7
    subst family
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))))))))))))))
  · have same : family=⟨8,by decide⟩ := Fin.ext h8
    subst family
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))))))))))))))

def numbers (w : TransferSem.Witness) (family : Fin 9) : Nat :=
  EncodedWordBits375.value w (valueColumn family)

theorem all_bounds (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem (crypto c) w) :
    ∀ family,numbers w family<TransferCore.scalarOrder :=
  fun family => ScalarCanonicalDomain394.scalar_bound c w legal (valueColumn family) (value_member family)

theorem all_bits (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (legal : TransferSem.TransferSem (crypto c) w) :
    ∀ family,∀ index<252,
      SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial
        (ScalarCanonicalRows395.bitStart family+index)=
      BinaryComparison100.bit (F:=F) ((encodeBits 252 (numbers w family))[index]?.getD false) := by
  intro family
  have known := role family
  have inside : SemanticWordFrame373.Inside (sourceWord family).1.value := by
    rw [known.1]
    exact ScalarCanonicalDomain394.inside (valueColumn family) (value_member family)
  have point := EncodedWordBits375.selected_bits original c w initial senderInitial receiverInitial legal
    (sourceWord family) (word_member family) inside
  rw [known.1,known.2.1,known.2.2] at point
  exact point

def Rows (rho : Nat → F) : Prop :=
  ∀ family : Fin 9,CompilerAssertionBlock51.SatisfiesAt rho
    (fun index => CapturedFullRelation58.rowAt (177954+ScalarCanonicalRows395.position family+index)) 2

theorem all_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (legal : TransferSem.TransferSem (crypto c) w) :
    Rows (SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial) := by
  let source := EncodedWordBits375.base original w senderInitial receiverInitial
  let rho := SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial
  have zero := SharedHighZeroRows333.zero (UserWordSeed342.seed source w) c w initial
  have linked := SharedComparisonBlocks327.linked (HighZeroSeed329.seed (UserWordSeed342.seed source w) w) c w initial
  have arithmetic := SharedHighZeroRows333.arithmetic (UserWordSeed342.seed source w) c w initial
  change rho 0=1 at zero
  change rho copy=rho 0 at linked
  change CompilerAssertionBlock51.SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954 at arithmetic
  exact ScalarCanonicalRows395.all_rows rho (numbers w) (all_bounds c w legal) zero (linked.trans zero) arithmetic
    (all_bits original c w initial senderInitial receiverInitial legal)

end ShielddSecurity.SharedScalarCanonical396

set_option pp.all true in
#check @ShielddSecurity.SharedScalarCanonical396.valueColumn
#print axioms ShielddSecurity.SharedScalarCanonical396.valueColumn

set_option pp.all true in
#check @ShielddSecurity.SharedScalarCanonical396.sourceWord
#print axioms ShielddSecurity.SharedScalarCanonical396.sourceWord

set_option pp.all true in
#check @ShielddSecurity.SharedScalarCanonical396.role_checked
#print axioms ShielddSecurity.SharedScalarCanonical396.role_checked

set_option pp.all true in
#check @ShielddSecurity.SharedScalarCanonical396.role
#print axioms ShielddSecurity.SharedScalarCanonical396.role

set_option pp.all true in
#check @ShielddSecurity.SharedScalarCanonical396.values_checked
#print axioms ShielddSecurity.SharedScalarCanonical396.values_checked

set_option pp.all true in
#check @ShielddSecurity.SharedScalarCanonical396.value_member
#print axioms ShielddSecurity.SharedScalarCanonical396.value_member

set_option pp.all true in
#check @ShielddSecurity.SharedScalarCanonical396.word_member
#print axioms ShielddSecurity.SharedScalarCanonical396.word_member

set_option pp.all true in
#check @ShielddSecurity.SharedScalarCanonical396.numbers
#print axioms ShielddSecurity.SharedScalarCanonical396.numbers

set_option pp.all true in
#check @ShielddSecurity.SharedScalarCanonical396.all_bounds
#print axioms ShielddSecurity.SharedScalarCanonical396.all_bounds

set_option pp.all true in
#check @ShielddSecurity.SharedScalarCanonical396.all_bits
#print axioms ShielddSecurity.SharedScalarCanonical396.all_bits

set_option pp.all true in
#check @ShielddSecurity.SharedScalarCanonical396.Rows
#print axioms ShielddSecurity.SharedScalarCanonical396.Rows

set_option pp.all true in
#check @ShielddSecurity.SharedScalarCanonical396.all_rows
#print axioms ShielddSecurity.SharedScalarCanonical396.all_rows
