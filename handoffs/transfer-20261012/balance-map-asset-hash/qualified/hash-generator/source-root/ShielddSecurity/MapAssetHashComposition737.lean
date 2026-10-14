/- Generated from maintained map asset-hash template. -/
import ShielddSecurity.MapAssetHashTail736B00
import ShielddSecurity.MapAssetHashTail736B01
import ShielddSecurity.MapAssetHashTail736B02
import ShielddSecurity.MapAssetHashTail736B03
import ShielddSecurity.MapAssetHashTail736B04
import ShielddSecurity.MapAssetHashTail736B05
import ShielddSecurity.MapAssetHashTail736B06
import ShielddSecurity.MapAssetHashTail736B07
import ShielddSecurity.MapAssetHashTail736B08
import ShielddSecurity.AuthorizationPoseidonChain519
import ShielddSecurity.TransferPoseidonWidth3Call08Semantic01
import ShielddSecurity.MapAssetHashCapture734C186B0R01
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapAssetHashComposition737
open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
open CapturedInitial73419Generic01 (p copy)
noncomputable def ren := CompilerWindowRenaming05.swap 24732 312 164599
noncomputable def before (index : Nat) (i : Fin 3) := linear ren (TransferPoseidonWidth3Call08Semantic01.before index i)
noncomputable def after (index : Nat) (i : Fin 3) := linear ren (TransferPoseidonWidth3Call08Semantic01.after index i)
theorem seam : before 2=MapAssetHashCapture734C186B0R01.after := by
  funext i
  have cases : i=0 ∨ i=1 ∨ i=2 := by have h:=i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl <;> decide +kernel
theorem boundary (index : Nat) (bound : index+1<65) : before (index+1)=after index := by
  unfold before after
  rw [TransferPoseidonWidth3Call08Semantic01.boundary index bound]
variable {F : Type} [Field F] [CharP F p]
theorem steps (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (index : Nat) (lower : 2 ≤ index) (upper : index<65) :
    (fun i => eval rho (after index i))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) index
      (fun i => eval rho (before index i)) := by
  have cases : index=2 ∨ index=3 ∨ index=4 ∨ index=5 ∨ index=6 ∨ index=7 ∨ index=8 ∨ index=9 ∨ index=10 ∨ index=11 ∨ index=12 ∨ index=13 ∨ index=14 ∨ index=15 ∨ index=16 ∨ index=17 ∨ index=18 ∨ index=19 ∨ index=20 ∨ index=21 ∨ index=22 ∨ index=23 ∨ index=24 ∨ index=25 ∨ index=26 ∨ index=27 ∨ index=28 ∨ index=29 ∨ index=30 ∨ index=31 ∨ index=32 ∨ index=33 ∨ index=34 ∨ index=35 ∨ index=36 ∨ index=37 ∨ index=38 ∨ index=39 ∨ index=40 ∨ index=41 ∨ index=42 ∨ index=43 ∨ index=44 ∨ index=45 ∨ index=46 ∨ index=47 ∨ index=48 ∨ index=49 ∨ index=50 ∨ index=51 ∨ index=52 ∨ index=53 ∨ index=54 ∨ index=55 ∨ index=56 ∨ index=57 ∨ index=58 ∨ index=59 ∨ index=60 ∨ index=61 ∨ index=62 ∨ index=63 ∨ index=64 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact MapAssetHashTail736B00.step2 rho one linked arithmetic
  · exact MapAssetHashTail736B00.step3 rho one linked arithmetic
  · exact MapAssetHashTail736B00.step4 rho one linked arithmetic
  · exact MapAssetHashTail736B00.step5 rho one linked arithmetic
  · exact MapAssetHashTail736B00.step6 rho one linked arithmetic
  · exact MapAssetHashTail736B00.step7 rho one linked arithmetic
  · exact MapAssetHashTail736B00.step8 rho one linked arithmetic
  · exact MapAssetHashTail736B01.step9 rho one linked arithmetic
  · exact MapAssetHashTail736B01.step10 rho one linked arithmetic
  · exact MapAssetHashTail736B01.step11 rho one linked arithmetic
  · exact MapAssetHashTail736B01.step12 rho one linked arithmetic
  · exact MapAssetHashTail736B01.step13 rho one linked arithmetic
  · exact MapAssetHashTail736B01.step14 rho one linked arithmetic
  · exact MapAssetHashTail736B01.step15 rho one linked arithmetic
  · exact MapAssetHashTail736B02.step16 rho one linked arithmetic
  · exact MapAssetHashTail736B02.step17 rho one linked arithmetic
  · exact MapAssetHashTail736B02.step18 rho one linked arithmetic
  · exact MapAssetHashTail736B02.step19 rho one linked arithmetic
  · exact MapAssetHashTail736B02.step20 rho one linked arithmetic
  · exact MapAssetHashTail736B02.step21 rho one linked arithmetic
  · exact MapAssetHashTail736B02.step22 rho one linked arithmetic
  · exact MapAssetHashTail736B03.step23 rho one linked arithmetic
  · exact MapAssetHashTail736B03.step24 rho one linked arithmetic
  · exact MapAssetHashTail736B03.step25 rho one linked arithmetic
  · exact MapAssetHashTail736B03.step26 rho one linked arithmetic
  · exact MapAssetHashTail736B03.step27 rho one linked arithmetic
  · exact MapAssetHashTail736B03.step28 rho one linked arithmetic
  · exact MapAssetHashTail736B03.step29 rho one linked arithmetic
  · exact MapAssetHashTail736B04.step30 rho one linked arithmetic
  · exact MapAssetHashTail736B04.step31 rho one linked arithmetic
  · exact MapAssetHashTail736B04.step32 rho one linked arithmetic
  · exact MapAssetHashTail736B04.step33 rho one linked arithmetic
  · exact MapAssetHashTail736B04.step34 rho one linked arithmetic
  · exact MapAssetHashTail736B04.step35 rho one linked arithmetic
  · exact MapAssetHashTail736B04.step36 rho one linked arithmetic
  · exact MapAssetHashTail736B05.step37 rho one linked arithmetic
  · exact MapAssetHashTail736B05.step38 rho one linked arithmetic
  · exact MapAssetHashTail736B05.step39 rho one linked arithmetic
  · exact MapAssetHashTail736B05.step40 rho one linked arithmetic
  · exact MapAssetHashTail736B05.step41 rho one linked arithmetic
  · exact MapAssetHashTail736B05.step42 rho one linked arithmetic
  · exact MapAssetHashTail736B05.step43 rho one linked arithmetic
  · exact MapAssetHashTail736B06.step44 rho one linked arithmetic
  · exact MapAssetHashTail736B06.step45 rho one linked arithmetic
  · exact MapAssetHashTail736B06.step46 rho one linked arithmetic
  · exact MapAssetHashTail736B06.step47 rho one linked arithmetic
  · exact MapAssetHashTail736B06.step48 rho one linked arithmetic
  · exact MapAssetHashTail736B06.step49 rho one linked arithmetic
  · exact MapAssetHashTail736B06.step50 rho one linked arithmetic
  · exact MapAssetHashTail736B07.step51 rho one linked arithmetic
  · exact MapAssetHashTail736B07.step52 rho one linked arithmetic
  · exact MapAssetHashTail736B07.step53 rho one linked arithmetic
  · exact MapAssetHashTail736B07.step54 rho one linked arithmetic
  · exact MapAssetHashTail736B07.step55 rho one linked arithmetic
  · exact MapAssetHashTail736B07.step56 rho one linked arithmetic
  · exact MapAssetHashTail736B07.step57 rho one linked arithmetic
  · exact MapAssetHashTail736B08.step58 rho one linked arithmetic
  · exact MapAssetHashTail736B08.step59 rho one linked arithmetic
  · exact MapAssetHashTail736B08.step60 rho one linked arithmetic
  · exact MapAssetHashTail736B08.step61 rho one linked arithmetic
  · exact MapAssetHashTail736B08.step62 rho one linked arithmetic
  · exact MapAssetHashTail736B08.step63 rho one linked arithmetic
  · exact MapAssetHashTail736B08.step64 rho one linked arithmetic
theorem suffix (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (after 64 i))=AuthorizationPoseidonChain519.roundsFrom
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 2 63
      (fun i => eval rho (MapAssetHashCapture734C186B0R01.after i)) := by
  have result := AuthorizationPoseidonChain519.suffix_chain
    (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 2 63
    (fun index i => eval rho (before index i)) (fun index i => eval rho (after index i))
    (by intro index bound;dsimp only;rw [boundary (2+index) (by omega)])
    (by intro index bound;exact steps rho one linked arithmetic (2+index) (by omega) (by omega)) 62 (by decide)
  dsimp only at result
  rw [seam] at result
  exact result
end ShielddSecurity.MapAssetHashComposition737
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashComposition737.seam
#print axioms ShielddSecurity.MapAssetHashComposition737.seam
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashComposition737.boundary
#print axioms ShielddSecurity.MapAssetHashComposition737.boundary
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashComposition737.steps
#print axioms ShielddSecurity.MapAssetHashComposition737.steps
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashComposition737.suffix
#print axioms ShielddSecurity.MapAssetHashComposition737.suffix
