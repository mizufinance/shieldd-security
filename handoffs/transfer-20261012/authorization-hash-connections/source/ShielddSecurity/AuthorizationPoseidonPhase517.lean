import ShielddSecurity.PoseidonIndexedFolded02
import ShielddSecurity.CapturedInitial73419Generic01
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationPoseidonPhase517
open Compiler CompilerIndexed01 Poseidon
open CapturedInitial73419Generic01 (p copy)
structure Data (width : Nat) where
  parameters : Parameters Int width
  index : Nat
  low : Nat
  high : Nat
  before : State Linear width
  shifted : State Linear width
  transformed : State Linear width
  after : State Linear width
  rows : List Row
  pivots : Fin width → Option Nat
  rowStarts : Fin width → Nat
  coefficients : Fin width → Int

def hints {width : Nat} (d : Data width) (i : Fin width) : PoseidonIndexedFolded02.FifthHint :=
  match d.pivots i with
  | none => .constant (d.coefficients i)
  | some column =>
    let row := d.rowStarts i
    .arithmetic ⟨[(column,1)],[(column+1,1)],[(column+3,1)],row,row+1,row+2,row+3⟩

variable {F : Type} [Field F] [CharP F p]
theorem four_ne_zero : (4:F)≠0 := by
  intro zero
  have divided := (CharP.cast_eq_zero_iff F p 4).mp zero
  have impossible : ¬p∣4 := by norm_num [p]
  exact impossible divided
/-- Soundness needs the checked round syntax and its rows, not a constructor's order certificate. -/
theorem arbitrary_round {width : Nat} (d : Data width)
    (checked : PoseidonIndexedFolded02.checkRound p copy d.rows.toArray d.parameters d.index
      d.before d.shifted d.transformed d.after (hints d)=true)
    (copyLink : checkRow p d.rows ⟨[(0,1),(copy,-1)],[]⟩=true)
    (rho : Nat → F) (one : rho 0=1) (sat : Satisfies rho d.rows) :
    (fun i => eval rho (d.after i))=Poseidon.round (castParameters d.parameters) d.index
      (fun i => eval rho (d.before i)) :=
  round_certificate_sound rho _ d.parameters d.index d.before d.shifted d.transformed d.after one
    four_ne_zero (unoutline_rows_sound rho copy d.rows sat copyLink)
    (PoseidonIndexedFolded02.checkRound_sound p copy _ d.parameters d.index d.before d.shifted
      d.transformed d.after (hints d) checked)
end ShielddSecurity.AuthorizationPoseidonPhase517
set_option pp.all true in
#check @ShielddSecurity.AuthorizationPoseidonPhase517.arbitrary_round
#print axioms ShielddSecurity.AuthorizationPoseidonPhase517.arbitrary_round
