import ShielddSecurity.SharedHighZeroRows333
import ShielddSecurity.CapturedValueCanonical107
import ShielddSecurity.CapturedAssetCanonical112
import ShielddSecurity.CapturedNextCanonical117
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedCanonicalRows340
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open HighZeroCompletionFrame332

theorem bit_interface (rho : Nat → F) (start n : Nat)
    (bits : ∀ index < 255, rho (start+index) =
      if (ShielddSecurity.encodeBits 255 n)[index]?.getD false then 1 else 0) :
    ∀ index < 255, rho (start+index) =
      BinaryComparison100.bit (F:=F) (CapturedValueComparison106.bitAt n (216+index)) := by
  intro index bound
  simpa only [CapturedValueComparison106.bitAt,Nat.add_sub_cancel_left,BinaryComparison100.bit] using bits index bound

theorem value_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    CompilerAssertionBlock51.SatisfiesAt (assignment original c w initial)
      (fun index => CapturedFullRelation58.rowAt (178375+index)) 2 := by
  have fields := RegistryWordBits322.value_bits (HighZeroSeed329.seed original w) c w initial legal
  change (∀ index < 255, assignment original c w initial (216+index) =
    if (ShielddSecurity.encodeBits 255 (w.registry.value))[index]?.getD false then 1 else 0) at fields
  have bits := bit_interface (assignment original c w initial) 216 (w.registry.value) fields
  rcases legal.2.1.1 with ⟨_,_,_,_,_,_,value,asset,next,_,_⟩
  have zero := SharedHighZeroRows333.zero original c w initial
  have linked := SharedComparisonBlocks327.linked (HighZeroSeed329.seed original w) c w initial
  exact CapturedValueCanonical107.complete (assignment original c w initial) (w.registry.value) value zero
    (linked.trans zero) (SharedHighZeroRows333.arithmetic original c w initial) bits

theorem asset_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    CompilerAssertionBlock51.SatisfiesAt (assignment original c w initial)
      (fun index => CapturedFullRelation58.rowAt (178633+index)) 2 := by
  have fields := RegistryWordBits322.asset_bits (HighZeroSeed329.seed original w) c w initial legal
  change (∀ index < 255, assignment original c w initial (471+index) =
    if (ShielddSecurity.encodeBits 255 (w.asset))[index]?.getD false then 1 else 0) at fields
  have bits := bit_interface (assignment original c w initial) 471 (w.asset) fields
  rcases legal.2.1.1 with ⟨_,_,_,_,_,_,value,asset,next,_,_⟩
  have zero := SharedHighZeroRows333.zero original c w initial
  have linked := SharedComparisonBlocks327.linked (HighZeroSeed329.seed original w) c w initial
  exact CapturedAssetCanonical112.complete (assignment original c w initial) (w.asset) asset zero
    (linked.trans zero) (SharedHighZeroRows333.arithmetic original c w initial) bits

theorem next_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    CompilerAssertionBlock51.SatisfiesAt (assignment original c w initial)
      (fun index => CapturedFullRelation58.rowAt (178891+index)) 2 := by
  have fields := RegistryWordBits322.next_bits (HighZeroSeed329.seed original w) c w initial legal
  change (∀ index < 255, assignment original c w initial (726+index) =
    if (ShielddSecurity.encodeBits 255 (w.registry.nextValue))[index]?.getD false then 1 else 0) at fields
  have bits := bit_interface (assignment original c w initial) 726 (w.registry.nextValue) fields
  rcases legal.2.1.1 with ⟨_,_,_,_,_,_,value,asset,next,_,_⟩
  have zero := SharedHighZeroRows333.zero original c w initial
  have linked := SharedComparisonBlocks327.linked (HighZeroSeed329.seed original w) c w initial
  exact CapturedNextCanonical117.complete (assignment original c w initial) (w.registry.nextValue) next zero
    (linked.trans zero) (SharedHighZeroRows333.arithmetic original c w initial) bits

def Rows (rho : Nat → F) : Prop :=
  CompilerAssertionBlock51.SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (178375+index)) 2 ∧
  CompilerAssertionBlock51.SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (178633+index)) 2 ∧
  CompilerAssertionBlock51.SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (178891+index)) 2

theorem all_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    Rows (assignment original c w initial) :=
  ⟨value_rows original c w initial legal,asset_rows original c w initial legal,next_rows original c w initial legal⟩
end ShielddSecurity.SharedCanonicalRows340

set_option pp.all true in
#check @ShielddSecurity.SharedCanonicalRows340.bit_interface
#print axioms ShielddSecurity.SharedCanonicalRows340.bit_interface

set_option pp.all true in
#check @ShielddSecurity.SharedCanonicalRows340.value_rows
#print axioms ShielddSecurity.SharedCanonicalRows340.value_rows

set_option pp.all true in
#check @ShielddSecurity.SharedCanonicalRows340.asset_rows
#print axioms ShielddSecurity.SharedCanonicalRows340.asset_rows

set_option pp.all true in
#check @ShielddSecurity.SharedCanonicalRows340.next_rows
#print axioms ShielddSecurity.SharedCanonicalRows340.next_rows

set_option pp.all true in
#check @ShielddSecurity.SharedCanonicalRows340.Rows
#print axioms ShielddSecurity.SharedCanonicalRows340.Rows

set_option pp.all true in
#check @ShielddSecurity.SharedCanonicalRows340.all_rows
#print axioms ShielddSecurity.SharedCanonicalRows340.all_rows
