-- GENERATED from entries.json by generate.py. Do not hand edit.
import ShielddSecurity.FixedPublishedRows580F00
import ShielddSecurity.FixedPublishedRows580F01
import ShielddSecurity.FixedPublishedRows580F02
import ShielddSecurity.FixedPublishedRows580F03
import ShielddSecurity.FixedPublishedRows580F04
import ShielddSecurity.FixedPublishedRows580F05
import ShielddSecurity.FixedPublishedRows580F06
import ShielddSecurity.FixedPublishedRows580F07
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.FixedPublishedRows580
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
def position (family : Fin 8) : Nat := [5292,6695,8826,10366,11906,13928,15194,16460][family.val]!
def leftColumn (family : Fin 8) : Nat := [5433,6837,9054,10586,12114,14132,15394,16656][family.val]!
def rightColumn (family : Fin 8) : Nat := [4922,6326,8547,10079,8515,8520,8526,8531][family.val]!
theorem rows_iff {F : Type} [Field F] [CharP F p] (rho : Nat → F) (family : Fin 8) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+position family+i)) 2 ↔
    VariableWindowColumns449.columnPoint rho (leftColumn family)=
      VariableWindowColumns449.columnPoint rho (rightColumn family) := by
  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ ∨ family=⟨2,by decide⟩ ∨
      family=⟨3,by decide⟩ ∨ family=⟨4,by decide⟩ ∨ family=⟨5,by decide⟩ ∨
      family=⟨6,by decide⟩ ∨ family=⟨7,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact FixedPublishedRows580F00.rows_iff rho
  · exact FixedPublishedRows580F01.rows_iff rho
  · exact FixedPublishedRows580F02.rows_iff rho
  · exact FixedPublishedRows580F03.rows_iff rho
  · exact FixedPublishedRows580F04.rows_iff rho
  · exact FixedPublishedRows580F05.rows_iff rho
  · exact FixedPublishedRows580F06.rows_iff rho
  · exact FixedPublishedRows580F07.rows_iff rho

end ShielddSecurity.FixedPublishedRows580

set_option pp.all true in
#check @ShielddSecurity.FixedPublishedRows580.position
#print axioms ShielddSecurity.FixedPublishedRows580.position

set_option pp.all true in
#check @ShielddSecurity.FixedPublishedRows580.leftColumn
#print axioms ShielddSecurity.FixedPublishedRows580.leftColumn

set_option pp.all true in
#check @ShielddSecurity.FixedPublishedRows580.rightColumn
#print axioms ShielddSecurity.FixedPublishedRows580.rightColumn

set_option pp.all true in
#check @ShielddSecurity.FixedPublishedRows580.rows_iff
#print axioms ShielddSecurity.FixedPublishedRows580.rows_iff
