/- Generated from maintained public statement-hash generator; edit generator or templates. -/
import ShielddSecurity.PublicStatementHashPermutation976C187B0
import ShielddSecurity.PublicStatementHashPermutation976C187B1
import ShielddSecurity.PublicStatementHashPermutation976C187B2
import ShielddSecurity.PublicStatementHashPermutation976C187B3
import ShielddSecurity.PublicStatementHashPermutation976C187B4
import ShielddSecurity.PublicStatementHashPermutation976C187B5
import ShielddSecurity.PublicStatementHashPermutation976C187B6
import ShielddSecurity.PublicStatementHashPermutation976C187B7
import ShielddSecurity.PublicStatementHashPermutation976C187B8
import ShielddSecurity.PublicStatementHashPermutation976C187B9
import ShielddSecurity.PublicStatementHashPermutation976C187B10
import ShielddSecurity.PublicStatementHashPermutation976C187B11
import ShielddSecurity.PublicStatementHashPermutation976C187B12
import ShielddSecurity.WideHashBlocks971
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PublicStatementHash977C187
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
noncomputable def parameters := PublicStatementHashPermutation976C187B0.parameters
noncomputable def result := PublicStatementHashPermutation976C187B12.result
noncomputable def inputs : List Linear := [[(4272,1)],[(4273,1)],[(3,1)],[(4920,1)],[(4921,1)],[(6324,1)],[(6325,1)],[(195230,1)],[(195234,1)],[(19848,1)],[(19849,1)],[(19589,1)],[(8509,1)],[(8510,1)],[(7739,1)],[(7607,1)],[(4532,1)],[(4785,1)],[(4,1)],[(5,1)],[(8511,1)],[(8512,1)],[(8513,1)],[(8514,1)],[(8515,1)],[(8516,1)],[(8517,1)],[(8519,1)],[(8520,1)],[(8521,1)],[(8522,1)],[(8523,1)],[(8524,1)],[(8525,1)],[(8526,1)],[(8527,1)],[(8528,1)],[(8530,1)],[(8531,1)],[(8532,1)],[(8533,1)],[(8534,1)],[(8535,1)],[(8536,1)],[(7,1)],[(8518,1)],[(8529,1)],[(8537,1)],[(8538,1)],[(8539,1)],[(8540,1)],[(8543,1)],[(8544,1)],[(8545,1)],[(8546,1)],[(8542,1)],[(8547,1)],[(8548,1)],[(8549,1)],[(8550,1)],[(10079,1)],[(10080,1)],[(10081,1)],[(10082,1)]]
variable {F : Type} [Field F] [CharP F p]
attribute [local irreducible] SatisfiesAt

noncomputable def parts (rho : Nat → F) : List (List F) :=
  [[eval rho [(4272,1)],eval rho [(4273,1)],eval rho [(3,1)],eval rho [(4920,1)],eval rho [(4921,1)]],[eval rho [(6324,1)],eval rho [(6325,1)],eval rho [(195230,1)],eval rho [(195234,1)],eval rho [(19848,1)]],[eval rho [(19849,1)],eval rho [(19589,1)],eval rho [(8509,1)],eval rho [(8510,1)],eval rho [(7739,1)]],[eval rho [(7607,1)],eval rho [(4532,1)],eval rho [(4785,1)],eval rho [(4,1)],eval rho [(5,1)]],[eval rho [(8511,1)],eval rho [(8512,1)],eval rho [(8513,1)],eval rho [(8514,1)],eval rho [(8515,1)]],[eval rho [(8516,1)],eval rho [(8517,1)],eval rho [(8519,1)],eval rho [(8520,1)],eval rho [(8521,1)]],[eval rho [(8522,1)],eval rho [(8523,1)],eval rho [(8524,1)],eval rho [(8525,1)],eval rho [(8526,1)]],[eval rho [(8527,1)],eval rho [(8528,1)],eval rho [(8530,1)],eval rho [(8531,1)],eval rho [(8532,1)]],[eval rho [(8533,1)],eval rho [(8534,1)],eval rho [(8535,1)],eval rho [(8536,1)],eval rho [(7,1)]],[eval rho [(8518,1)],eval rho [(8529,1)],eval rho [(8537,1)],eval rho [(8538,1)],eval rho [(8539,1)]],[eval rho [(8540,1)],eval rho [(8543,1)],eval rho [(8544,1)],eval rho [(8545,1)],eval rho [(8546,1)]],[eval rho [(8542,1)],eval rho [(8547,1)],eval rho [(8548,1)],eval rho [(8549,1)],eval rho [(8550,1)]],[eval rho [(10079,1)],eval rho [(10080,1)],eval rho [(10081,1)],eval rho [(10082,1)]]]

noncomputable def states (rho : Nat → F) : Nat → Poseidon.State F 6
  | 0 => Poseidon.initial 34 64
  | 1 => fun j => eval rho (PublicStatementHashPermutation976C187B0.after j)
  | 2 => fun j => eval rho (PublicStatementHashPermutation976C187B1.after j)
  | 3 => fun j => eval rho (PublicStatementHashPermutation976C187B2.after j)
  | 4 => fun j => eval rho (PublicStatementHashPermutation976C187B3.after j)
  | 5 => fun j => eval rho (PublicStatementHashPermutation976C187B4.after j)
  | 6 => fun j => eval rho (PublicStatementHashPermutation976C187B5.after j)
  | 7 => fun j => eval rho (PublicStatementHashPermutation976C187B6.after j)
  | 8 => fun j => eval rho (PublicStatementHashPermutation976C187B7.after j)
  | 9 => fun j => eval rho (PublicStatementHashPermutation976C187B8.after j)
  | 10 => fun j => eval rho (PublicStatementHashPermutation976C187B9.after j)
  | 11 => fun j => eval rho (PublicStatementHashPermutation976C187B10.after j)
  | 12 => fun j => eval rho (PublicStatementHashPermutation976C187B11.after j)
  | 13 => fun j => eval rho (PublicStatementHashPermutation976C187B12.after j)
  | _ => fun _ => 0
theorem chunks (rho : Nat → F) : Poseidon.chunks5 (inputs.map (eval rho))=parts rho := rfl

theorem initial (rho : Nat → F) (one : rho 0=1) :
    (fun i => eval rho (PublicStatementHashPermutation976C187B0.before i))=Poseidon.absorb (Poseidon.initial 34 64) ((parts rho).get ⟨0,by change 0 < 13; decide⟩) := by
  funext i
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by have h:=i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · change eval rho [(0,16418)]=((16418:Nat):F)
    norm_num [eval,one]
  · change eval rho [(4272,1)]=0+eval rho [(4272,1)]
    exact (zero_add _).symm
  · change eval rho [(4273,1)]=0+eval rho [(4273,1)]
    exact (zero_add _).symm
  · change eval rho [(3,1)]=0+eval rho [(3,1)]
    exact (zero_add _).symm
  · change eval rho [(4920,1)]=0+eval rho [(4920,1)]
    exact (zero_add _).symm
  · change eval rho [(4921,1)]=0+eval rho [(4921,1)]
    exact (zero_add _).symm
theorem continuation1_0_shape : canonical p (PublicStatementHashPermutation976C187B1.before 0)=canonical p (PublicStatementHashPermutation976C187B0.after 0) := by decide +kernel
theorem continuation1_1_shape : canonical p (PublicStatementHashPermutation976C187B1.before 1)=canonical p (PublicStatementHashPermutation976C187B0.after 1++[(6324,1)]) := by decide +kernel
theorem continuation1_2_shape : canonical p (PublicStatementHashPermutation976C187B1.before 2)=canonical p (PublicStatementHashPermutation976C187B0.after 2++[(6325,1)]) := by decide +kernel
theorem continuation1_3_shape : canonical p (PublicStatementHashPermutation976C187B1.before 3)=canonical p (PublicStatementHashPermutation976C187B0.after 3++[(195230,1)]) := by decide +kernel
theorem continuation1_4_shape : canonical p (PublicStatementHashPermutation976C187B1.before 4)=canonical p (PublicStatementHashPermutation976C187B0.after 4++[(195234,1)]) := by decide +kernel
theorem continuation1_5_shape : canonical p (PublicStatementHashPermutation976C187B1.before 5)=canonical p (PublicStatementHashPermutation976C187B0.after 5++[(19848,1)]) := by decide +kernel
theorem continuation1 (rho : Nat → F) :
    (fun j => eval rho (PublicStatementHashPermutation976C187B1.before j))=Poseidon.absorb (fun j => eval rho (PublicStatementHashPermutation976C187B0.after j)) ((parts rho).get ⟨1,by change 1 < 13; decide⟩) := by
  funext j
  have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by have h:=j.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · change eval rho (PublicStatementHashPermutation976C187B1.before 0)=eval rho (PublicStatementHashPermutation976C187B0.after 0)
    exact canonical_equal rho _ _ continuation1_0_shape
  · change eval rho (PublicStatementHashPermutation976C187B1.before 1)=eval rho (PublicStatementHashPermutation976C187B0.after 1)+eval rho [(6324,1)]
    rw [canonical_equal rho _ _ continuation1_1_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B1.before 2)=eval rho (PublicStatementHashPermutation976C187B0.after 2)+eval rho [(6325,1)]
    rw [canonical_equal rho _ _ continuation1_2_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B1.before 3)=eval rho (PublicStatementHashPermutation976C187B0.after 3)+eval rho [(195230,1)]
    rw [canonical_equal rho _ _ continuation1_3_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B1.before 4)=eval rho (PublicStatementHashPermutation976C187B0.after 4)+eval rho [(195234,1)]
    rw [canonical_equal rho _ _ continuation1_4_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B1.before 5)=eval rho (PublicStatementHashPermutation976C187B0.after 5)+eval rho [(19848,1)]
    rw [canonical_equal rho _ _ continuation1_5_shape,eval_append]
theorem continuation2_0_shape : canonical p (PublicStatementHashPermutation976C187B2.before 0)=canonical p (PublicStatementHashPermutation976C187B1.after 0) := by decide +kernel
theorem continuation2_1_shape : canonical p (PublicStatementHashPermutation976C187B2.before 1)=canonical p (PublicStatementHashPermutation976C187B1.after 1++[(19849,1)]) := by decide +kernel
theorem continuation2_2_shape : canonical p (PublicStatementHashPermutation976C187B2.before 2)=canonical p (PublicStatementHashPermutation976C187B1.after 2++[(19589,1)]) := by decide +kernel
theorem continuation2_3_shape : canonical p (PublicStatementHashPermutation976C187B2.before 3)=canonical p (PublicStatementHashPermutation976C187B1.after 3++[(8509,1)]) := by decide +kernel
theorem continuation2_4_shape : canonical p (PublicStatementHashPermutation976C187B2.before 4)=canonical p (PublicStatementHashPermutation976C187B1.after 4++[(8510,1)]) := by decide +kernel
theorem continuation2_5_shape : canonical p (PublicStatementHashPermutation976C187B2.before 5)=canonical p (PublicStatementHashPermutation976C187B1.after 5++[(7739,1)]) := by decide +kernel
theorem continuation2 (rho : Nat → F) :
    (fun j => eval rho (PublicStatementHashPermutation976C187B2.before j))=Poseidon.absorb (fun j => eval rho (PublicStatementHashPermutation976C187B1.after j)) ((parts rho).get ⟨2,by change 2 < 13; decide⟩) := by
  funext j
  have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by have h:=j.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · change eval rho (PublicStatementHashPermutation976C187B2.before 0)=eval rho (PublicStatementHashPermutation976C187B1.after 0)
    exact canonical_equal rho _ _ continuation2_0_shape
  · change eval rho (PublicStatementHashPermutation976C187B2.before 1)=eval rho (PublicStatementHashPermutation976C187B1.after 1)+eval rho [(19849,1)]
    rw [canonical_equal rho _ _ continuation2_1_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B2.before 2)=eval rho (PublicStatementHashPermutation976C187B1.after 2)+eval rho [(19589,1)]
    rw [canonical_equal rho _ _ continuation2_2_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B2.before 3)=eval rho (PublicStatementHashPermutation976C187B1.after 3)+eval rho [(8509,1)]
    rw [canonical_equal rho _ _ continuation2_3_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B2.before 4)=eval rho (PublicStatementHashPermutation976C187B1.after 4)+eval rho [(8510,1)]
    rw [canonical_equal rho _ _ continuation2_4_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B2.before 5)=eval rho (PublicStatementHashPermutation976C187B1.after 5)+eval rho [(7739,1)]
    rw [canonical_equal rho _ _ continuation2_5_shape,eval_append]
theorem continuation3_0_shape : canonical p (PublicStatementHashPermutation976C187B3.before 0)=canonical p (PublicStatementHashPermutation976C187B2.after 0) := by decide +kernel
theorem continuation3_1_shape : canonical p (PublicStatementHashPermutation976C187B3.before 1)=canonical p (PublicStatementHashPermutation976C187B2.after 1++[(7607,1)]) := by decide +kernel
theorem continuation3_2_shape : canonical p (PublicStatementHashPermutation976C187B3.before 2)=canonical p (PublicStatementHashPermutation976C187B2.after 2++[(4532,1)]) := by decide +kernel
theorem continuation3_3_shape : canonical p (PublicStatementHashPermutation976C187B3.before 3)=canonical p (PublicStatementHashPermutation976C187B2.after 3++[(4785,1)]) := by decide +kernel
theorem continuation3_4_shape : canonical p (PublicStatementHashPermutation976C187B3.before 4)=canonical p (PublicStatementHashPermutation976C187B2.after 4++[(4,1)]) := by decide +kernel
theorem continuation3_5_shape : canonical p (PublicStatementHashPermutation976C187B3.before 5)=canonical p (PublicStatementHashPermutation976C187B2.after 5++[(5,1)]) := by decide +kernel
theorem continuation3 (rho : Nat → F) :
    (fun j => eval rho (PublicStatementHashPermutation976C187B3.before j))=Poseidon.absorb (fun j => eval rho (PublicStatementHashPermutation976C187B2.after j)) ((parts rho).get ⟨3,by change 3 < 13; decide⟩) := by
  funext j
  have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by have h:=j.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · change eval rho (PublicStatementHashPermutation976C187B3.before 0)=eval rho (PublicStatementHashPermutation976C187B2.after 0)
    exact canonical_equal rho _ _ continuation3_0_shape
  · change eval rho (PublicStatementHashPermutation976C187B3.before 1)=eval rho (PublicStatementHashPermutation976C187B2.after 1)+eval rho [(7607,1)]
    rw [canonical_equal rho _ _ continuation3_1_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B3.before 2)=eval rho (PublicStatementHashPermutation976C187B2.after 2)+eval rho [(4532,1)]
    rw [canonical_equal rho _ _ continuation3_2_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B3.before 3)=eval rho (PublicStatementHashPermutation976C187B2.after 3)+eval rho [(4785,1)]
    rw [canonical_equal rho _ _ continuation3_3_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B3.before 4)=eval rho (PublicStatementHashPermutation976C187B2.after 4)+eval rho [(4,1)]
    rw [canonical_equal rho _ _ continuation3_4_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B3.before 5)=eval rho (PublicStatementHashPermutation976C187B2.after 5)+eval rho [(5,1)]
    rw [canonical_equal rho _ _ continuation3_5_shape,eval_append]
theorem continuation4_0_shape : canonical p (PublicStatementHashPermutation976C187B4.before 0)=canonical p (PublicStatementHashPermutation976C187B3.after 0) := by decide +kernel
theorem continuation4_1_shape : canonical p (PublicStatementHashPermutation976C187B4.before 1)=canonical p (PublicStatementHashPermutation976C187B3.after 1++[(8511,1)]) := by decide +kernel
theorem continuation4_2_shape : canonical p (PublicStatementHashPermutation976C187B4.before 2)=canonical p (PublicStatementHashPermutation976C187B3.after 2++[(8512,1)]) := by decide +kernel
theorem continuation4_3_shape : canonical p (PublicStatementHashPermutation976C187B4.before 3)=canonical p (PublicStatementHashPermutation976C187B3.after 3++[(8513,1)]) := by decide +kernel
theorem continuation4_4_shape : canonical p (PublicStatementHashPermutation976C187B4.before 4)=canonical p (PublicStatementHashPermutation976C187B3.after 4++[(8514,1)]) := by decide +kernel
theorem continuation4_5_shape : canonical p (PublicStatementHashPermutation976C187B4.before 5)=canonical p (PublicStatementHashPermutation976C187B3.after 5++[(8515,1)]) := by decide +kernel
theorem continuation4 (rho : Nat → F) :
    (fun j => eval rho (PublicStatementHashPermutation976C187B4.before j))=Poseidon.absorb (fun j => eval rho (PublicStatementHashPermutation976C187B3.after j)) ((parts rho).get ⟨4,by change 4 < 13; decide⟩) := by
  funext j
  have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by have h:=j.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · change eval rho (PublicStatementHashPermutation976C187B4.before 0)=eval rho (PublicStatementHashPermutation976C187B3.after 0)
    exact canonical_equal rho _ _ continuation4_0_shape
  · change eval rho (PublicStatementHashPermutation976C187B4.before 1)=eval rho (PublicStatementHashPermutation976C187B3.after 1)+eval rho [(8511,1)]
    rw [canonical_equal rho _ _ continuation4_1_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B4.before 2)=eval rho (PublicStatementHashPermutation976C187B3.after 2)+eval rho [(8512,1)]
    rw [canonical_equal rho _ _ continuation4_2_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B4.before 3)=eval rho (PublicStatementHashPermutation976C187B3.after 3)+eval rho [(8513,1)]
    rw [canonical_equal rho _ _ continuation4_3_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B4.before 4)=eval rho (PublicStatementHashPermutation976C187B3.after 4)+eval rho [(8514,1)]
    rw [canonical_equal rho _ _ continuation4_4_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B4.before 5)=eval rho (PublicStatementHashPermutation976C187B3.after 5)+eval rho [(8515,1)]
    rw [canonical_equal rho _ _ continuation4_5_shape,eval_append]
theorem continuation5_0_shape : canonical p (PublicStatementHashPermutation976C187B5.before 0)=canonical p (PublicStatementHashPermutation976C187B4.after 0) := by decide +kernel
theorem continuation5_1_shape : canonical p (PublicStatementHashPermutation976C187B5.before 1)=canonical p (PublicStatementHashPermutation976C187B4.after 1++[(8516,1)]) := by decide +kernel
theorem continuation5_2_shape : canonical p (PublicStatementHashPermutation976C187B5.before 2)=canonical p (PublicStatementHashPermutation976C187B4.after 2++[(8517,1)]) := by decide +kernel
theorem continuation5_3_shape : canonical p (PublicStatementHashPermutation976C187B5.before 3)=canonical p (PublicStatementHashPermutation976C187B4.after 3++[(8519,1)]) := by decide +kernel
theorem continuation5_4_shape : canonical p (PublicStatementHashPermutation976C187B5.before 4)=canonical p (PublicStatementHashPermutation976C187B4.after 4++[(8520,1)]) := by decide +kernel
theorem continuation5_5_shape : canonical p (PublicStatementHashPermutation976C187B5.before 5)=canonical p (PublicStatementHashPermutation976C187B4.after 5++[(8521,1)]) := by decide +kernel
theorem continuation5 (rho : Nat → F) :
    (fun j => eval rho (PublicStatementHashPermutation976C187B5.before j))=Poseidon.absorb (fun j => eval rho (PublicStatementHashPermutation976C187B4.after j)) ((parts rho).get ⟨5,by change 5 < 13; decide⟩) := by
  funext j
  have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by have h:=j.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · change eval rho (PublicStatementHashPermutation976C187B5.before 0)=eval rho (PublicStatementHashPermutation976C187B4.after 0)
    exact canonical_equal rho _ _ continuation5_0_shape
  · change eval rho (PublicStatementHashPermutation976C187B5.before 1)=eval rho (PublicStatementHashPermutation976C187B4.after 1)+eval rho [(8516,1)]
    rw [canonical_equal rho _ _ continuation5_1_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B5.before 2)=eval rho (PublicStatementHashPermutation976C187B4.after 2)+eval rho [(8517,1)]
    rw [canonical_equal rho _ _ continuation5_2_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B5.before 3)=eval rho (PublicStatementHashPermutation976C187B4.after 3)+eval rho [(8519,1)]
    rw [canonical_equal rho _ _ continuation5_3_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B5.before 4)=eval rho (PublicStatementHashPermutation976C187B4.after 4)+eval rho [(8520,1)]
    rw [canonical_equal rho _ _ continuation5_4_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B5.before 5)=eval rho (PublicStatementHashPermutation976C187B4.after 5)+eval rho [(8521,1)]
    rw [canonical_equal rho _ _ continuation5_5_shape,eval_append]
theorem continuation6_0_shape : canonical p (PublicStatementHashPermutation976C187B6.before 0)=canonical p (PublicStatementHashPermutation976C187B5.after 0) := by decide +kernel
theorem continuation6_1_shape : canonical p (PublicStatementHashPermutation976C187B6.before 1)=canonical p (PublicStatementHashPermutation976C187B5.after 1++[(8522,1)]) := by decide +kernel
theorem continuation6_2_shape : canonical p (PublicStatementHashPermutation976C187B6.before 2)=canonical p (PublicStatementHashPermutation976C187B5.after 2++[(8523,1)]) := by decide +kernel
theorem continuation6_3_shape : canonical p (PublicStatementHashPermutation976C187B6.before 3)=canonical p (PublicStatementHashPermutation976C187B5.after 3++[(8524,1)]) := by decide +kernel
theorem continuation6_4_shape : canonical p (PublicStatementHashPermutation976C187B6.before 4)=canonical p (PublicStatementHashPermutation976C187B5.after 4++[(8525,1)]) := by decide +kernel
theorem continuation6_5_shape : canonical p (PublicStatementHashPermutation976C187B6.before 5)=canonical p (PublicStatementHashPermutation976C187B5.after 5++[(8526,1)]) := by decide +kernel
theorem continuation6 (rho : Nat → F) :
    (fun j => eval rho (PublicStatementHashPermutation976C187B6.before j))=Poseidon.absorb (fun j => eval rho (PublicStatementHashPermutation976C187B5.after j)) ((parts rho).get ⟨6,by change 6 < 13; decide⟩) := by
  funext j
  have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by have h:=j.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · change eval rho (PublicStatementHashPermutation976C187B6.before 0)=eval rho (PublicStatementHashPermutation976C187B5.after 0)
    exact canonical_equal rho _ _ continuation6_0_shape
  · change eval rho (PublicStatementHashPermutation976C187B6.before 1)=eval rho (PublicStatementHashPermutation976C187B5.after 1)+eval rho [(8522,1)]
    rw [canonical_equal rho _ _ continuation6_1_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B6.before 2)=eval rho (PublicStatementHashPermutation976C187B5.after 2)+eval rho [(8523,1)]
    rw [canonical_equal rho _ _ continuation6_2_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B6.before 3)=eval rho (PublicStatementHashPermutation976C187B5.after 3)+eval rho [(8524,1)]
    rw [canonical_equal rho _ _ continuation6_3_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B6.before 4)=eval rho (PublicStatementHashPermutation976C187B5.after 4)+eval rho [(8525,1)]
    rw [canonical_equal rho _ _ continuation6_4_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B6.before 5)=eval rho (PublicStatementHashPermutation976C187B5.after 5)+eval rho [(8526,1)]
    rw [canonical_equal rho _ _ continuation6_5_shape,eval_append]
theorem continuation7_0_shape : canonical p (PublicStatementHashPermutation976C187B7.before 0)=canonical p (PublicStatementHashPermutation976C187B6.after 0) := by decide +kernel
theorem continuation7_1_shape : canonical p (PublicStatementHashPermutation976C187B7.before 1)=canonical p (PublicStatementHashPermutation976C187B6.after 1++[(8527,1)]) := by decide +kernel
theorem continuation7_2_shape : canonical p (PublicStatementHashPermutation976C187B7.before 2)=canonical p (PublicStatementHashPermutation976C187B6.after 2++[(8528,1)]) := by decide +kernel
theorem continuation7_3_shape : canonical p (PublicStatementHashPermutation976C187B7.before 3)=canonical p (PublicStatementHashPermutation976C187B6.after 3++[(8530,1)]) := by decide +kernel
theorem continuation7_4_shape : canonical p (PublicStatementHashPermutation976C187B7.before 4)=canonical p (PublicStatementHashPermutation976C187B6.after 4++[(8531,1)]) := by decide +kernel
theorem continuation7_5_shape : canonical p (PublicStatementHashPermutation976C187B7.before 5)=canonical p (PublicStatementHashPermutation976C187B6.after 5++[(8532,1)]) := by decide +kernel
theorem continuation7 (rho : Nat → F) :
    (fun j => eval rho (PublicStatementHashPermutation976C187B7.before j))=Poseidon.absorb (fun j => eval rho (PublicStatementHashPermutation976C187B6.after j)) ((parts rho).get ⟨7,by change 7 < 13; decide⟩) := by
  funext j
  have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by have h:=j.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · change eval rho (PublicStatementHashPermutation976C187B7.before 0)=eval rho (PublicStatementHashPermutation976C187B6.after 0)
    exact canonical_equal rho _ _ continuation7_0_shape
  · change eval rho (PublicStatementHashPermutation976C187B7.before 1)=eval rho (PublicStatementHashPermutation976C187B6.after 1)+eval rho [(8527,1)]
    rw [canonical_equal rho _ _ continuation7_1_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B7.before 2)=eval rho (PublicStatementHashPermutation976C187B6.after 2)+eval rho [(8528,1)]
    rw [canonical_equal rho _ _ continuation7_2_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B7.before 3)=eval rho (PublicStatementHashPermutation976C187B6.after 3)+eval rho [(8530,1)]
    rw [canonical_equal rho _ _ continuation7_3_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B7.before 4)=eval rho (PublicStatementHashPermutation976C187B6.after 4)+eval rho [(8531,1)]
    rw [canonical_equal rho _ _ continuation7_4_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B7.before 5)=eval rho (PublicStatementHashPermutation976C187B6.after 5)+eval rho [(8532,1)]
    rw [canonical_equal rho _ _ continuation7_5_shape,eval_append]
theorem continuation8_0_shape : canonical p (PublicStatementHashPermutation976C187B8.before 0)=canonical p (PublicStatementHashPermutation976C187B7.after 0) := by decide +kernel
theorem continuation8_1_shape : canonical p (PublicStatementHashPermutation976C187B8.before 1)=canonical p (PublicStatementHashPermutation976C187B7.after 1++[(8533,1)]) := by decide +kernel
theorem continuation8_2_shape : canonical p (PublicStatementHashPermutation976C187B8.before 2)=canonical p (PublicStatementHashPermutation976C187B7.after 2++[(8534,1)]) := by decide +kernel
theorem continuation8_3_shape : canonical p (PublicStatementHashPermutation976C187B8.before 3)=canonical p (PublicStatementHashPermutation976C187B7.after 3++[(8535,1)]) := by decide +kernel
theorem continuation8_4_shape : canonical p (PublicStatementHashPermutation976C187B8.before 4)=canonical p (PublicStatementHashPermutation976C187B7.after 4++[(8536,1)]) := by decide +kernel
theorem continuation8_5_shape : canonical p (PublicStatementHashPermutation976C187B8.before 5)=canonical p (PublicStatementHashPermutation976C187B7.after 5++[(7,1)]) := by decide +kernel
theorem continuation8 (rho : Nat → F) :
    (fun j => eval rho (PublicStatementHashPermutation976C187B8.before j))=Poseidon.absorb (fun j => eval rho (PublicStatementHashPermutation976C187B7.after j)) ((parts rho).get ⟨8,by change 8 < 13; decide⟩) := by
  funext j
  have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by have h:=j.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · change eval rho (PublicStatementHashPermutation976C187B8.before 0)=eval rho (PublicStatementHashPermutation976C187B7.after 0)
    exact canonical_equal rho _ _ continuation8_0_shape
  · change eval rho (PublicStatementHashPermutation976C187B8.before 1)=eval rho (PublicStatementHashPermutation976C187B7.after 1)+eval rho [(8533,1)]
    rw [canonical_equal rho _ _ continuation8_1_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B8.before 2)=eval rho (PublicStatementHashPermutation976C187B7.after 2)+eval rho [(8534,1)]
    rw [canonical_equal rho _ _ continuation8_2_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B8.before 3)=eval rho (PublicStatementHashPermutation976C187B7.after 3)+eval rho [(8535,1)]
    rw [canonical_equal rho _ _ continuation8_3_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B8.before 4)=eval rho (PublicStatementHashPermutation976C187B7.after 4)+eval rho [(8536,1)]
    rw [canonical_equal rho _ _ continuation8_4_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B8.before 5)=eval rho (PublicStatementHashPermutation976C187B7.after 5)+eval rho [(7,1)]
    rw [canonical_equal rho _ _ continuation8_5_shape,eval_append]
theorem continuation9_0_shape : canonical p (PublicStatementHashPermutation976C187B9.before 0)=canonical p (PublicStatementHashPermutation976C187B8.after 0) := by decide +kernel
theorem continuation9_1_shape : canonical p (PublicStatementHashPermutation976C187B9.before 1)=canonical p (PublicStatementHashPermutation976C187B8.after 1++[(8518,1)]) := by decide +kernel
theorem continuation9_2_shape : canonical p (PublicStatementHashPermutation976C187B9.before 2)=canonical p (PublicStatementHashPermutation976C187B8.after 2++[(8529,1)]) := by decide +kernel
theorem continuation9_3_shape : canonical p (PublicStatementHashPermutation976C187B9.before 3)=canonical p (PublicStatementHashPermutation976C187B8.after 3++[(8537,1)]) := by decide +kernel
theorem continuation9_4_shape : canonical p (PublicStatementHashPermutation976C187B9.before 4)=canonical p (PublicStatementHashPermutation976C187B8.after 4++[(8538,1)]) := by decide +kernel
theorem continuation9_5_shape : canonical p (PublicStatementHashPermutation976C187B9.before 5)=canonical p (PublicStatementHashPermutation976C187B8.after 5++[(8539,1)]) := by decide +kernel
theorem continuation9 (rho : Nat → F) :
    (fun j => eval rho (PublicStatementHashPermutation976C187B9.before j))=Poseidon.absorb (fun j => eval rho (PublicStatementHashPermutation976C187B8.after j)) ((parts rho).get ⟨9,by change 9 < 13; decide⟩) := by
  funext j
  have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by have h:=j.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · change eval rho (PublicStatementHashPermutation976C187B9.before 0)=eval rho (PublicStatementHashPermutation976C187B8.after 0)
    exact canonical_equal rho _ _ continuation9_0_shape
  · change eval rho (PublicStatementHashPermutation976C187B9.before 1)=eval rho (PublicStatementHashPermutation976C187B8.after 1)+eval rho [(8518,1)]
    rw [canonical_equal rho _ _ continuation9_1_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B9.before 2)=eval rho (PublicStatementHashPermutation976C187B8.after 2)+eval rho [(8529,1)]
    rw [canonical_equal rho _ _ continuation9_2_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B9.before 3)=eval rho (PublicStatementHashPermutation976C187B8.after 3)+eval rho [(8537,1)]
    rw [canonical_equal rho _ _ continuation9_3_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B9.before 4)=eval rho (PublicStatementHashPermutation976C187B8.after 4)+eval rho [(8538,1)]
    rw [canonical_equal rho _ _ continuation9_4_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B9.before 5)=eval rho (PublicStatementHashPermutation976C187B8.after 5)+eval rho [(8539,1)]
    rw [canonical_equal rho _ _ continuation9_5_shape,eval_append]
theorem continuation10_0_shape : canonical p (PublicStatementHashPermutation976C187B10.before 0)=canonical p (PublicStatementHashPermutation976C187B9.after 0) := by decide +kernel
theorem continuation10_1_shape : canonical p (PublicStatementHashPermutation976C187B10.before 1)=canonical p (PublicStatementHashPermutation976C187B9.after 1++[(8540,1)]) := by decide +kernel
theorem continuation10_2_shape : canonical p (PublicStatementHashPermutation976C187B10.before 2)=canonical p (PublicStatementHashPermutation976C187B9.after 2++[(8543,1)]) := by decide +kernel
theorem continuation10_3_shape : canonical p (PublicStatementHashPermutation976C187B10.before 3)=canonical p (PublicStatementHashPermutation976C187B9.after 3++[(8544,1)]) := by decide +kernel
theorem continuation10_4_shape : canonical p (PublicStatementHashPermutation976C187B10.before 4)=canonical p (PublicStatementHashPermutation976C187B9.after 4++[(8545,1)]) := by decide +kernel
theorem continuation10_5_shape : canonical p (PublicStatementHashPermutation976C187B10.before 5)=canonical p (PublicStatementHashPermutation976C187B9.after 5++[(8546,1)]) := by decide +kernel
theorem continuation10 (rho : Nat → F) :
    (fun j => eval rho (PublicStatementHashPermutation976C187B10.before j))=Poseidon.absorb (fun j => eval rho (PublicStatementHashPermutation976C187B9.after j)) ((parts rho).get ⟨10,by change 10 < 13; decide⟩) := by
  funext j
  have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by have h:=j.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · change eval rho (PublicStatementHashPermutation976C187B10.before 0)=eval rho (PublicStatementHashPermutation976C187B9.after 0)
    exact canonical_equal rho _ _ continuation10_0_shape
  · change eval rho (PublicStatementHashPermutation976C187B10.before 1)=eval rho (PublicStatementHashPermutation976C187B9.after 1)+eval rho [(8540,1)]
    rw [canonical_equal rho _ _ continuation10_1_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B10.before 2)=eval rho (PublicStatementHashPermutation976C187B9.after 2)+eval rho [(8543,1)]
    rw [canonical_equal rho _ _ continuation10_2_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B10.before 3)=eval rho (PublicStatementHashPermutation976C187B9.after 3)+eval rho [(8544,1)]
    rw [canonical_equal rho _ _ continuation10_3_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B10.before 4)=eval rho (PublicStatementHashPermutation976C187B9.after 4)+eval rho [(8545,1)]
    rw [canonical_equal rho _ _ continuation10_4_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B10.before 5)=eval rho (PublicStatementHashPermutation976C187B9.after 5)+eval rho [(8546,1)]
    rw [canonical_equal rho _ _ continuation10_5_shape,eval_append]
theorem continuation11_0_shape : canonical p (PublicStatementHashPermutation976C187B11.before 0)=canonical p (PublicStatementHashPermutation976C187B10.after 0) := by decide +kernel
theorem continuation11_1_shape : canonical p (PublicStatementHashPermutation976C187B11.before 1)=canonical p (PublicStatementHashPermutation976C187B10.after 1++[(8542,1)]) := by decide +kernel
theorem continuation11_2_shape : canonical p (PublicStatementHashPermutation976C187B11.before 2)=canonical p (PublicStatementHashPermutation976C187B10.after 2++[(8547,1)]) := by decide +kernel
theorem continuation11_3_shape : canonical p (PublicStatementHashPermutation976C187B11.before 3)=canonical p (PublicStatementHashPermutation976C187B10.after 3++[(8548,1)]) := by decide +kernel
theorem continuation11_4_shape : canonical p (PublicStatementHashPermutation976C187B11.before 4)=canonical p (PublicStatementHashPermutation976C187B10.after 4++[(8549,1)]) := by decide +kernel
theorem continuation11_5_shape : canonical p (PublicStatementHashPermutation976C187B11.before 5)=canonical p (PublicStatementHashPermutation976C187B10.after 5++[(8550,1)]) := by decide +kernel
theorem continuation11 (rho : Nat → F) :
    (fun j => eval rho (PublicStatementHashPermutation976C187B11.before j))=Poseidon.absorb (fun j => eval rho (PublicStatementHashPermutation976C187B10.after j)) ((parts rho).get ⟨11,by change 11 < 13; decide⟩) := by
  funext j
  have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by have h:=j.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · change eval rho (PublicStatementHashPermutation976C187B11.before 0)=eval rho (PublicStatementHashPermutation976C187B10.after 0)
    exact canonical_equal rho _ _ continuation11_0_shape
  · change eval rho (PublicStatementHashPermutation976C187B11.before 1)=eval rho (PublicStatementHashPermutation976C187B10.after 1)+eval rho [(8542,1)]
    rw [canonical_equal rho _ _ continuation11_1_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B11.before 2)=eval rho (PublicStatementHashPermutation976C187B10.after 2)+eval rho [(8547,1)]
    rw [canonical_equal rho _ _ continuation11_2_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B11.before 3)=eval rho (PublicStatementHashPermutation976C187B10.after 3)+eval rho [(8548,1)]
    rw [canonical_equal rho _ _ continuation11_3_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B11.before 4)=eval rho (PublicStatementHashPermutation976C187B10.after 4)+eval rho [(8549,1)]
    rw [canonical_equal rho _ _ continuation11_4_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B11.before 5)=eval rho (PublicStatementHashPermutation976C187B10.after 5)+eval rho [(8550,1)]
    rw [canonical_equal rho _ _ continuation11_5_shape,eval_append]
theorem continuation12_0_shape : canonical p (PublicStatementHashPermutation976C187B12.before 0)=canonical p (PublicStatementHashPermutation976C187B11.after 0) := by decide +kernel
theorem continuation12_1_shape : canonical p (PublicStatementHashPermutation976C187B12.before 1)=canonical p (PublicStatementHashPermutation976C187B11.after 1++[(10079,1)]) := by decide +kernel
theorem continuation12_2_shape : canonical p (PublicStatementHashPermutation976C187B12.before 2)=canonical p (PublicStatementHashPermutation976C187B11.after 2++[(10080,1)]) := by decide +kernel
theorem continuation12_3_shape : canonical p (PublicStatementHashPermutation976C187B12.before 3)=canonical p (PublicStatementHashPermutation976C187B11.after 3++[(10081,1)]) := by decide +kernel
theorem continuation12_4_shape : canonical p (PublicStatementHashPermutation976C187B12.before 4)=canonical p (PublicStatementHashPermutation976C187B11.after 4++[(10082,1)]) := by decide +kernel
theorem continuation12_5_shape : canonical p (PublicStatementHashPermutation976C187B12.before 5)=canonical p (PublicStatementHashPermutation976C187B11.after 5) := by decide +kernel
theorem continuation12 (rho : Nat → F) :
    (fun j => eval rho (PublicStatementHashPermutation976C187B12.before j))=Poseidon.absorb (fun j => eval rho (PublicStatementHashPermutation976C187B11.after j)) ((parts rho).get ⟨12,by change 12 < 13; decide⟩) := by
  funext j
  have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by have h:=j.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · change eval rho (PublicStatementHashPermutation976C187B12.before 0)=eval rho (PublicStatementHashPermutation976C187B11.after 0)
    exact canonical_equal rho _ _ continuation12_0_shape
  · change eval rho (PublicStatementHashPermutation976C187B12.before 1)=eval rho (PublicStatementHashPermutation976C187B11.after 1)+eval rho [(10079,1)]
    rw [canonical_equal rho _ _ continuation12_1_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B12.before 2)=eval rho (PublicStatementHashPermutation976C187B11.after 2)+eval rho [(10080,1)]
    rw [canonical_equal rho _ _ continuation12_2_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B12.before 3)=eval rho (PublicStatementHashPermutation976C187B11.after 3)+eval rho [(10081,1)]
    rw [canonical_equal rho _ _ continuation12_3_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B12.before 4)=eval rho (PublicStatementHashPermutation976C187B11.after 4)+eval rho [(10082,1)]
    rw [canonical_equal rho _ _ continuation12_4_shape,eval_append]
  · change eval rho (PublicStatementHashPermutation976C187B12.before 5)=eval rho (PublicStatementHashPermutation976C187B11.after 5)+0
    rw [canonical_equal rho _ _ continuation12_5_shape,add_zero]
theorem hash (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    eval rho result=Poseidon.hash6 (Poseidon.castParameters parameters) 34 (inputs.map (eval rho)) := by
  have block0 := PublicStatementHashPermutation976C187B0.permutation rho one linked arithmetic
  rw [initial rho one] at block0
  have block1 := PublicStatementHashPermutation976C187B1.permutation rho one linked arithmetic
  rw [continuation1 rho] at block1
  have block2 := PublicStatementHashPermutation976C187B2.permutation rho one linked arithmetic
  rw [continuation2 rho] at block2
  have block3 := PublicStatementHashPermutation976C187B3.permutation rho one linked arithmetic
  rw [continuation3 rho] at block3
  have block4 := PublicStatementHashPermutation976C187B4.permutation rho one linked arithmetic
  rw [continuation4 rho] at block4
  have block5 := PublicStatementHashPermutation976C187B5.permutation rho one linked arithmetic
  rw [continuation5 rho] at block5
  have block6 := PublicStatementHashPermutation976C187B6.permutation rho one linked arithmetic
  rw [continuation6 rho] at block6
  have block7 := PublicStatementHashPermutation976C187B7.permutation rho one linked arithmetic
  rw [continuation7 rho] at block7
  have block8 := PublicStatementHashPermutation976C187B8.permutation rho one linked arithmetic
  rw [continuation8 rho] at block8
  have block9 := PublicStatementHashPermutation976C187B9.permutation rho one linked arithmetic
  rw [continuation9 rho] at block9
  have block10 := PublicStatementHashPermutation976C187B10.permutation rho one linked arithmetic
  rw [continuation10 rho] at block10
  have block11 := PublicStatementHashPermutation976C187B11.permutation rho one linked arithmetic
  rw [continuation11 rho] at block11
  have block12 := PublicStatementHashPermutation976C187B12.permutation rho one linked arithmetic
  rw [continuation12 rho] at block12
  have advance : ∀ i (inside : i<13), states rho (i+1)=
      Poseidon.permute (Poseidon.castParameters parameters) (Poseidon.absorb (states rho i) (parts rho)[i]) := by
    intro i inside
    match i with
    | 0 => exact block0
    | 1 => exact block1
    | 2 => exact block2
    | 3 => exact block3
    | 4 => exact block4
    | 5 => exact block5
    | 6 => exact block6
    | 7 => exact block7
    | 8 => exact block8
    | 9 => exact block9
    | 10 => exact block10
    | 11 => exact block11
    | 12 => exact block12
    | n+13 => omega
  have joined := WideHashBlocks971.hash (Poseidon.castParameters parameters) 34 (inputs.map (eval rho))
    (parts rho) (states rho) (chunks rho) (by intro h;cases h) rfl advance
  simpa only [parts,states,PublicStatementHashPermutation976C187B12.result_port,result] using joined
end ShielddSecurity.PublicStatementHash977C187

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.chunks
#print axioms ShielddSecurity.PublicStatementHash977C187.chunks

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.initial
#print axioms ShielddSecurity.PublicStatementHash977C187.initial

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation1_0_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation1_0_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation1_1_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation1_1_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation1_2_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation1_2_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation1_3_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation1_3_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation1_4_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation1_4_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation1_5_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation1_5_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation1
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation1

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation2_0_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation2_0_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation2_1_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation2_1_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation2_2_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation2_2_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation2_3_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation2_3_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation2_4_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation2_4_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation2_5_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation2_5_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation2
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation2

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation3_0_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation3_0_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation3_1_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation3_1_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation3_2_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation3_2_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation3_3_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation3_3_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation3_4_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation3_4_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation3_5_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation3_5_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation3
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation3

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation4_0_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation4_0_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation4_1_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation4_1_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation4_2_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation4_2_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation4_3_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation4_3_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation4_4_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation4_4_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation4_5_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation4_5_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation4
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation4

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation5_0_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation5_0_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation5_1_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation5_1_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation5_2_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation5_2_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation5_3_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation5_3_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation5_4_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation5_4_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation5_5_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation5_5_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation5
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation5

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation6_0_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation6_0_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation6_1_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation6_1_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation6_2_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation6_2_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation6_3_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation6_3_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation6_4_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation6_4_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation6_5_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation6_5_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation6
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation6

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation7_0_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation7_0_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation7_1_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation7_1_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation7_2_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation7_2_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation7_3_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation7_3_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation7_4_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation7_4_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation7_5_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation7_5_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation7
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation7

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation8_0_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation8_0_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation8_1_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation8_1_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation8_2_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation8_2_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation8_3_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation8_3_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation8_4_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation8_4_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation8_5_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation8_5_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation8
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation8

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation9_0_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation9_0_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation9_1_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation9_1_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation9_2_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation9_2_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation9_3_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation9_3_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation9_4_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation9_4_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation9_5_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation9_5_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation9
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation9

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation10_0_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation10_0_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation10_1_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation10_1_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation10_2_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation10_2_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation10_3_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation10_3_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation10_4_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation10_4_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation10_5_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation10_5_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation10
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation10

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation11_0_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation11_0_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation11_1_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation11_1_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation11_2_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation11_2_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation11_3_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation11_3_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation11_4_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation11_4_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation11_5_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation11_5_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation11
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation11

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation12_0_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation12_0_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation12_1_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation12_1_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation12_2_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation12_2_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation12_3_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation12_3_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation12_4_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation12_4_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation12_5_shape
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation12_5_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.continuation12
#print axioms ShielddSecurity.PublicStatementHash977C187.continuation12

set_option pp.all true in
#check @ShielddSecurity.PublicStatementHash977C187.hash
#print axioms ShielddSecurity.PublicStatementHash977C187.hash
