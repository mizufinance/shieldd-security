/- Generated from maintained volume output-hash generator; edit generator or templates. -/
import ShielddSecurity.VolumeOutputHashTail915C150B00
import ShielddSecurity.VolumeOutputHashTail915C150B01
import ShielddSecurity.VolumeOutputHashTail915C150B02
import ShielddSecurity.VolumeOutputHashTail915C150B03
import ShielddSecurity.VolumeOutputHashTail915C150B04
import ShielddSecurity.VolumeOutputHashTail915C150B05
import ShielddSecurity.VolumeOutputHashTail915C150B06
import ShielddSecurity.VolumeOutputHashTail915C150B07
import ShielddSecurity.VolumeOutputHashTail915C150B08
import ShielddSecurity.VolumeOutputHashTail915C150B09
import ShielddSecurity.VolumeOutputHashTail915C150B10
import ShielddSecurity.VolumeOutputHashTail915C150B11
import ShielddSecurity.VolumeOutputHashTail915C150B12
import ShielddSecurity.VolumeOutputHashTail915C150B13
import ShielddSecurity.VolumeOutputHashTail915C150B14
import ShielddSecurity.VolumeOutputHashTail915C150B15
import ShielddSecurity.VolumeOutputHashTail915C150B16
import ShielddSecurity.VolumeOutputHashTail915C150B17
import ShielddSecurity.VolumeOutputHashTail915C150B18
import ShielddSecurity.VolumeOutputHashTail915C150B19
import ShielddSecurity.VolumeOutputHashTail915C150B20
import ShielddSecurity.AuthorizationPoseidonChain519
import ShielddSecurity.TransferPoseidonCall04Semantic01
import ShielddSecurity.VolumeOutputHashCapture913C150B0R01
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeOutputHashComposition916C150
open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
open CapturedInitial73419Generic01 (p copy)
noncomputable def ren := CompilerWindowRenaming05.swap 23076 396 96852
noncomputable def before (index : Nat) (i : Fin 6) := linear ren (TransferPoseidonCall04Semantic01.before index i)
noncomputable def after (index : Nat) (i : Fin 6) := linear ren (TransferPoseidonCall04Semantic01.after index i)
theorem seam : before 2=VolumeOutputHashCapture913C150B0R01.after := by
  funext i
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by have h:=i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
theorem boundary (index : Nat) (bound : index+1<65) : before (index+1)=after index := by
  unfold before after
  rw [TransferPoseidonCall04Semantic01.boundary index bound]
variable {F : Type} [Field F] [CharP F p]
theorem steps (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (index : Nat) (lower : 2 ≤ index) (upper : index<65) :
    (fun i => eval rho (after index i))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) index
      (fun i => eval rho (before index i)) := by
  match index with
  | 0 => omega
  | 1 => omega
  | 2 => exact VolumeOutputHashTail915C150B00.step2 rho one linked arithmetic
  | 3 => exact VolumeOutputHashTail915C150B00.step3 rho one linked arithmetic
  | 4 => exact VolumeOutputHashTail915C150B00.step4 rho one linked arithmetic
  | 5 => exact VolumeOutputHashTail915C150B01.step5 rho one linked arithmetic
  | 6 => exact VolumeOutputHashTail915C150B01.step6 rho one linked arithmetic
  | 7 => exact VolumeOutputHashTail915C150B01.step7 rho one linked arithmetic
  | 8 => exact VolumeOutputHashTail915C150B02.step8 rho one linked arithmetic
  | 9 => exact VolumeOutputHashTail915C150B02.step9 rho one linked arithmetic
  | 10 => exact VolumeOutputHashTail915C150B02.step10 rho one linked arithmetic
  | 11 => exact VolumeOutputHashTail915C150B03.step11 rho one linked arithmetic
  | 12 => exact VolumeOutputHashTail915C150B03.step12 rho one linked arithmetic
  | 13 => exact VolumeOutputHashTail915C150B03.step13 rho one linked arithmetic
  | 14 => exact VolumeOutputHashTail915C150B04.step14 rho one linked arithmetic
  | 15 => exact VolumeOutputHashTail915C150B04.step15 rho one linked arithmetic
  | 16 => exact VolumeOutputHashTail915C150B04.step16 rho one linked arithmetic
  | 17 => exact VolumeOutputHashTail915C150B05.step17 rho one linked arithmetic
  | 18 => exact VolumeOutputHashTail915C150B05.step18 rho one linked arithmetic
  | 19 => exact VolumeOutputHashTail915C150B05.step19 rho one linked arithmetic
  | 20 => exact VolumeOutputHashTail915C150B06.step20 rho one linked arithmetic
  | 21 => exact VolumeOutputHashTail915C150B06.step21 rho one linked arithmetic
  | 22 => exact VolumeOutputHashTail915C150B06.step22 rho one linked arithmetic
  | 23 => exact VolumeOutputHashTail915C150B07.step23 rho one linked arithmetic
  | 24 => exact VolumeOutputHashTail915C150B07.step24 rho one linked arithmetic
  | 25 => exact VolumeOutputHashTail915C150B07.step25 rho one linked arithmetic
  | 26 => exact VolumeOutputHashTail915C150B08.step26 rho one linked arithmetic
  | 27 => exact VolumeOutputHashTail915C150B08.step27 rho one linked arithmetic
  | 28 => exact VolumeOutputHashTail915C150B08.step28 rho one linked arithmetic
  | 29 => exact VolumeOutputHashTail915C150B09.step29 rho one linked arithmetic
  | 30 => exact VolumeOutputHashTail915C150B09.step30 rho one linked arithmetic
  | 31 => exact VolumeOutputHashTail915C150B09.step31 rho one linked arithmetic
  | 32 => exact VolumeOutputHashTail915C150B10.step32 rho one linked arithmetic
  | 33 => exact VolumeOutputHashTail915C150B10.step33 rho one linked arithmetic
  | 34 => exact VolumeOutputHashTail915C150B10.step34 rho one linked arithmetic
  | 35 => exact VolumeOutputHashTail915C150B11.step35 rho one linked arithmetic
  | 36 => exact VolumeOutputHashTail915C150B11.step36 rho one linked arithmetic
  | 37 => exact VolumeOutputHashTail915C150B11.step37 rho one linked arithmetic
  | 38 => exact VolumeOutputHashTail915C150B12.step38 rho one linked arithmetic
  | 39 => exact VolumeOutputHashTail915C150B12.step39 rho one linked arithmetic
  | 40 => exact VolumeOutputHashTail915C150B12.step40 rho one linked arithmetic
  | 41 => exact VolumeOutputHashTail915C150B13.step41 rho one linked arithmetic
  | 42 => exact VolumeOutputHashTail915C150B13.step42 rho one linked arithmetic
  | 43 => exact VolumeOutputHashTail915C150B13.step43 rho one linked arithmetic
  | 44 => exact VolumeOutputHashTail915C150B14.step44 rho one linked arithmetic
  | 45 => exact VolumeOutputHashTail915C150B14.step45 rho one linked arithmetic
  | 46 => exact VolumeOutputHashTail915C150B14.step46 rho one linked arithmetic
  | 47 => exact VolumeOutputHashTail915C150B15.step47 rho one linked arithmetic
  | 48 => exact VolumeOutputHashTail915C150B15.step48 rho one linked arithmetic
  | 49 => exact VolumeOutputHashTail915C150B15.step49 rho one linked arithmetic
  | 50 => exact VolumeOutputHashTail915C150B16.step50 rho one linked arithmetic
  | 51 => exact VolumeOutputHashTail915C150B16.step51 rho one linked arithmetic
  | 52 => exact VolumeOutputHashTail915C150B16.step52 rho one linked arithmetic
  | 53 => exact VolumeOutputHashTail915C150B17.step53 rho one linked arithmetic
  | 54 => exact VolumeOutputHashTail915C150B17.step54 rho one linked arithmetic
  | 55 => exact VolumeOutputHashTail915C150B17.step55 rho one linked arithmetic
  | 56 => exact VolumeOutputHashTail915C150B18.step56 rho one linked arithmetic
  | 57 => exact VolumeOutputHashTail915C150B18.step57 rho one linked arithmetic
  | 58 => exact VolumeOutputHashTail915C150B18.step58 rho one linked arithmetic
  | 59 => exact VolumeOutputHashTail915C150B19.step59 rho one linked arithmetic
  | 60 => exact VolumeOutputHashTail915C150B19.step60 rho one linked arithmetic
  | 61 => exact VolumeOutputHashTail915C150B19.step61 rho one linked arithmetic
  | 62 => exact VolumeOutputHashTail915C150B20.step62 rho one linked arithmetic
  | 63 => exact VolumeOutputHashTail915C150B20.step63 rho one linked arithmetic
  | 64 => exact VolumeOutputHashTail915C150B20.step64 rho one linked arithmetic
  | n+65 => omega
theorem suffix (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (after 64 i))=AuthorizationPoseidonChain519.roundsFrom
      (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 2 63
      (fun i => eval rho (VolumeOutputHashCapture913C150B0R01.after i)) := by
  have result := AuthorizationPoseidonChain519.suffix_chain
    (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 2 63
    (fun index i => eval rho (before index i)) (fun index i => eval rho (after index i))
    (by intro index bound;dsimp only;rw [boundary (2+index) (by omega)])
    (by intro index bound;exact steps rho one linked arithmetic (2+index) (by omega) (by omega)) 62 (by decide)
  dsimp only at result
  rw [seam] at result
  exact result
end ShielddSecurity.VolumeOutputHashComposition916C150
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashComposition916C150.seam
#print axioms ShielddSecurity.VolumeOutputHashComposition916C150.seam
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashComposition916C150.boundary
#print axioms ShielddSecurity.VolumeOutputHashComposition916C150.boundary
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashComposition916C150.steps
#print axioms ShielddSecurity.VolumeOutputHashComposition916C150.steps
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashComposition916C150.suffix
#print axioms ShielddSecurity.VolumeOutputHashComposition916C150.suffix
