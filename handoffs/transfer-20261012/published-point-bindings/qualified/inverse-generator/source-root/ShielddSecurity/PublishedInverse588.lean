-- GENERATED from entries.json by generate.py. Do not hand edit.
import ShielddSecurity.PublishedInverse588F00
import ShielddSecurity.PublishedInverse588F01
import ShielddSecurity.PublishedInverse588F02
import ShielddSecurity.PublishedInverse588F03
import ShielddSecurity.PublishedInverse588F04
import ShielddSecurity.PublishedInverse588F05
import ShielddSecurity.PublishedInverse588F06
import ShielddSecurity.PublishedInverse588F07
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PublishedInverse588
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
def position (family : Fin 8) : Nat := [5294,6697,8828,10368,11908,13930,15196,16462][family.val]!
def operand (family : Fin 8) : Nat := [4922,6326,8547,10079,8515,8520,8526,8531][family.val]!
def hint (family : Fin 8) : Nat := [5435,6839,9056,10588,12116,14134,15396,16658][family.val]!
def output (family : Fin 8) : Nat := [91126,101453,124080,132405,142310,154384,161677,168970][family.val]!
variable {F : Type} [Field F] [CharP F p]
def Rows (rho : Nat → F) (family : Fin 8) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+(position family+i))) 1
theorem products (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (family : Fin 8) : rho (output family)=rho (operand family)*rho (hint family) := by
  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ ∨ family=⟨2,by decide⟩ ∨
      family=⟨3,by decide⟩ ∨ family=⟨4,by decide⟩ ∨ family=⟨5,by decide⟩ ∨
      family=⟨6,by decide⟩ ∨ family=⟨7,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · simpa only [PublishedInverse588F00.output,PublishedInverse588F00.arithmeticStart,PublishedInverse588F00.operandTerms,PublishedInverse588F00.hintColumn,eval,Int.cast_one,one_mul,add_zero] using PublishedInverse588F00.products rho arithmetic 0 (by decide)
  · simpa only [PublishedInverse588F01.output,PublishedInverse588F01.arithmeticStart,PublishedInverse588F01.operandTerms,PublishedInverse588F01.hintColumn,eval,Int.cast_one,one_mul,add_zero] using PublishedInverse588F01.products rho arithmetic 0 (by decide)
  · simpa only [PublishedInverse588F02.output,PublishedInverse588F02.arithmeticStart,PublishedInverse588F02.operandTerms,PublishedInverse588F02.hintColumn,eval,Int.cast_one,one_mul,add_zero] using PublishedInverse588F02.products rho arithmetic 0 (by decide)
  · simpa only [PublishedInverse588F03.output,PublishedInverse588F03.arithmeticStart,PublishedInverse588F03.operandTerms,PublishedInverse588F03.hintColumn,eval,Int.cast_one,one_mul,add_zero] using PublishedInverse588F03.products rho arithmetic 0 (by decide)
  · simpa only [PublishedInverse588F04.output,PublishedInverse588F04.arithmeticStart,PublishedInverse588F04.operandTerms,PublishedInverse588F04.hintColumn,eval,Int.cast_one,one_mul,add_zero] using PublishedInverse588F04.products rho arithmetic 0 (by decide)
  · simpa only [PublishedInverse588F05.output,PublishedInverse588F05.arithmeticStart,PublishedInverse588F05.operandTerms,PublishedInverse588F05.hintColumn,eval,Int.cast_one,one_mul,add_zero] using PublishedInverse588F05.products rho arithmetic 0 (by decide)
  · simpa only [PublishedInverse588F06.output,PublishedInverse588F06.arithmeticStart,PublishedInverse588F06.operandTerms,PublishedInverse588F06.hintColumn,eval,Int.cast_one,one_mul,add_zero] using PublishedInverse588F06.products rho arithmetic 0 (by decide)
  · simpa only [PublishedInverse588F07.output,PublishedInverse588F07.arithmeticStart,PublishedInverse588F07.operandTerms,PublishedInverse588F07.hintColumn,eval,Int.cast_one,one_mul,add_zero] using PublishedInverse588F07.products rho arithmetic 0 (by decide)
theorem complete (rho : Nat → F) (zero : rho 0=1) (linked : rho copy=rho 0)
    (family : Fin 8) (value : rho (output family)=1) : Rows rho family := by
  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ ∨ family=⟨2,by decide⟩ ∨
      family=⟨3,by decide⟩ ∨ family=⟨4,by decide⟩ ∨ family=⟨5,by decide⟩ ∨
      family=⟨6,by decide⟩ ∨ family=⟨7,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · apply PublishedInverse588F00.complete rho zero linked
    intro index bound
    have equal : index=0 := by omega
    subst index
    exact value
  · apply PublishedInverse588F01.complete rho zero linked
    intro index bound
    have equal : index=0 := by omega
    subst index
    exact value
  · apply PublishedInverse588F02.complete rho zero linked
    intro index bound
    have equal : index=0 := by omega
    subst index
    exact value
  · apply PublishedInverse588F03.complete rho zero linked
    intro index bound
    have equal : index=0 := by omega
    subst index
    exact value
  · apply PublishedInverse588F04.complete rho zero linked
    intro index bound
    have equal : index=0 := by omega
    subst index
    exact value
  · apply PublishedInverse588F05.complete rho zero linked
    intro index bound
    have equal : index=0 := by omega
    subst index
    exact value
  · apply PublishedInverse588F06.complete rho zero linked
    intro index bound
    have equal : index=0 := by omega
    subst index
    exact value
  · apply PublishedInverse588F07.complete rho zero linked
    intro index bound
    have equal : index=0 := by omega
    subst index
    exact value
theorem sound (rho : Nat → F) (zero : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (family : Fin 8) (rows : Rows rho family) : rho (operand family)≠0 := by
  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ ∨ family=⟨2,by decide⟩ ∨
      family=⟨3,by decide⟩ ∨ family=⟨4,by decide⟩ ∨ family=⟨5,by decide⟩ ∨
      family=⟨6,by decide⟩ ∨ family=⟨7,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · simpa only [PublishedInverse588F00.operandTerms,eval,Int.cast_one,one_mul,add_zero] using PublishedInverse588F00.sound rho zero linked arithmetic rows 0 (by decide)
  · simpa only [PublishedInverse588F01.operandTerms,eval,Int.cast_one,one_mul,add_zero] using PublishedInverse588F01.sound rho zero linked arithmetic rows 0 (by decide)
  · simpa only [PublishedInverse588F02.operandTerms,eval,Int.cast_one,one_mul,add_zero] using PublishedInverse588F02.sound rho zero linked arithmetic rows 0 (by decide)
  · simpa only [PublishedInverse588F03.operandTerms,eval,Int.cast_one,one_mul,add_zero] using PublishedInverse588F03.sound rho zero linked arithmetic rows 0 (by decide)
  · simpa only [PublishedInverse588F04.operandTerms,eval,Int.cast_one,one_mul,add_zero] using PublishedInverse588F04.sound rho zero linked arithmetic rows 0 (by decide)
  · simpa only [PublishedInverse588F05.operandTerms,eval,Int.cast_one,one_mul,add_zero] using PublishedInverse588F05.sound rho zero linked arithmetic rows 0 (by decide)
  · simpa only [PublishedInverse588F06.operandTerms,eval,Int.cast_one,one_mul,add_zero] using PublishedInverse588F06.sound rho zero linked arithmetic rows 0 (by decide)
  · simpa only [PublishedInverse588F07.operandTerms,eval,Int.cast_one,one_mul,add_zero] using PublishedInverse588F07.sound rho zero linked arithmetic rows 0 (by decide)
end ShielddSecurity.PublishedInverse588

set_option pp.all true in
#check @ShielddSecurity.PublishedInverse588.position
#print axioms ShielddSecurity.PublishedInverse588.position

set_option pp.all true in
#check @ShielddSecurity.PublishedInverse588.operand
#print axioms ShielddSecurity.PublishedInverse588.operand

set_option pp.all true in
#check @ShielddSecurity.PublishedInverse588.hint
#print axioms ShielddSecurity.PublishedInverse588.hint

set_option pp.all true in
#check @ShielddSecurity.PublishedInverse588.output
#print axioms ShielddSecurity.PublishedInverse588.output

set_option pp.all true in
#check @ShielddSecurity.PublishedInverse588.Rows
#print axioms ShielddSecurity.PublishedInverse588.Rows

set_option pp.all true in
#check @ShielddSecurity.PublishedInverse588.products
#print axioms ShielddSecurity.PublishedInverse588.products

set_option pp.all true in
#check @ShielddSecurity.PublishedInverse588.complete
#print axioms ShielddSecurity.PublishedInverse588.complete

set_option pp.all true in
#check @ShielddSecurity.PublishedInverse588.sound
#print axioms ShielddSecurity.PublishedInverse588.sound
