import ShielddSecurity.BinaryComparison100
import ShielddSecurity.CompilerArithmeticTransport41
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.ComparisonCertificate101
open Compiler CompilerArithmeticTransport41
structure Entry where
  bitColumn : Nat
  maximumBit : Bool
  before : Linear
  after : Linear
  pivot : Nat
  auxiliary : Nat
  rows : List Row

def right (entry : Entry) : Linear :=
  if entry.maximumBit then [(entry.bitColumn,1)] else [(copy,1),(entry.bitColumn,-1)]
def expectedAfter (entry : Entry) : Linear :=
  if entry.maximumBit then [(copy,1),(entry.bitColumn,-1),(entry.pivot,1)] else [(entry.pivot,1)]
def check (entry : Entry) : Bool :=
  decide (canonical p entry.after=canonical p (expectedAfter entry)) &&
    (checkRow p entry.rows ⟨subtract entry.before (right entry),[(entry.auxiliary,1)]⟩ &&
     checkRow p entry.rows ⟨entry.before++right entry,[(entry.auxiliary,1)]++scaleLinear 4 [(entry.pivot,1)]⟩)

variable {F : Type} [Field F]
theorem entry_sound [CharP F p] (rho : Nat → F) (entry : Entry)
    (one : rho copy=1) (checked : check entry=true) (satisfied : Satisfies rho entry.rows) :
    eval rho entry.after=BinaryComparison100.step (eval rho entry.before) (rho entry.bitColumn)
      (BinaryComparison100.bit entry.maximumBit) := by
  have checks:=Bool.and_eq_true_iff.mp checked
  have product:=Bool.and_eq_true_iff.mp checks.2
  have port:=canonical_equal rho entry.after (expectedAfter entry) (of_decide_eq_true checks.1)
  have value:=checked_product_sound rho entry.rows entry.before (right entry) [(entry.pivot,1)] [(entry.auxiliary,1)]
    four_ne_zero satisfied product.1 product.2
  cases flag : entry.maximumBit
  · have r : right entry=[(copy,1),(entry.bitColumn,-1)] := by simp only [right,flag,if_false]
    have a : expectedAfter entry=[(entry.pivot,1)] := by simp only [expectedAfter,flag,if_false]
    rw [r] at value
    rw [a] at port
    have v : rho entry.pivot=eval rho entry.before*(1-rho entry.bitColumn) := by
      simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,neg_mul,add_zero,one,sub_eq_add_neg] using value
    calc
      eval rho entry.after=rho entry.pivot := port.trans (by simp only [eval,Int.cast_one,one_mul,add_zero])
      _ = BinaryComparison100.step (eval rho entry.before) (rho entry.bitColumn) (BinaryComparison100.bit entry.maximumBit) := by
        rw [v,flag]
        change eval rho entry.before*(1-rho entry.bitColumn)=
          (1-rho entry.bitColumn)*0+eval rho entry.before*((1-rho entry.bitColumn)+0-((1-rho entry.bitColumn)*0+(1-rho entry.bitColumn)*0))
        ring
  · have r : right entry=[(entry.bitColumn,1)] := by simp only [right,flag,if_true]
    have a : expectedAfter entry=[(copy,1),(entry.bitColumn,-1),(entry.pivot,1)] := by simp only [expectedAfter,flag,if_true]
    rw [r] at value
    rw [a] at port
    have v : rho entry.pivot=eval rho entry.before*rho entry.bitColumn := by
      simpa only [eval,Int.cast_one,one_mul,add_zero] using value
    calc
      eval rho entry.after=1-rho entry.bitColumn+rho entry.pivot := by
        simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,neg_mul,add_zero,one,sub_eq_add_neg,add_assoc] using port
      _ = BinaryComparison100.step (eval rho entry.before) (rho entry.bitColumn) (BinaryComparison100.bit entry.maximumBit) := by
        rw [v,flag]
        change 1-rho entry.bitColumn+eval rho entry.before*rho entry.bitColumn=
          (1-rho entry.bitColumn)*1+eval rho entry.before*((1-rho entry.bitColumn)+1-((1-rho entry.bitColumn)*1+(1-rho entry.bitColumn)*1))
        ring

def chainCheck (initial : Linear) : List Entry → Bool
  | [] => true
  | entry::tail => decide (canonical p initial=canonical p entry.before) && (check entry && chainCheck entry.after tail)
def output (initial : Linear) : List Entry → Linear
  | [] => initial
  | entry::tail => output entry.after tail

def rawScan (rho : Nat → F) (flag : F) : List Entry → F
  | [] => flag
  | entry::tail => rawScan rho
      (BinaryComparison100.step flag (rho entry.bitColumn) (BinaryComparison100.bit entry.maximumBit)) tail

theorem chain_sound [CharP F p] (rho : Nat → F) (initial : Linear) (entries : List Entry)
    (one : rho copy=1) (checked : chainCheck initial entries=true)
    (satisfied : Satisfies rho (entries.flatMap Entry.rows)) :
    eval rho (output initial entries)=rawScan rho (eval rho initial) entries := by
  induction entries generalizing initial with
  | nil => rfl
  | cons entry tail ih =>
    have checks:=Bool.and_eq_true_iff.mp checked
    have rest:=Bool.and_eq_true_iff.mp checks.2
    have before:=canonical_equal rho initial entry.before (of_decide_eq_true checks.1)
    have entrySat : Satisfies rho entry.rows := by
      intro row member
      exact satisfied row (List.mem_append_left _ member)
    have tailSat : Satisfies rho (tail.flatMap Entry.rows) := by
      intro row member
      exact satisfied row (List.mem_append_right _ member)
    have value:=entry_sound rho entry one rest.1 entrySat
    rw [←before] at value
    exact (ih entry.after rest.2 tailSat).trans (congrArg (fun flag => rawScan rho flag tail) value)

theorem rawScan_boolean (rho : Nat → F) (flag : F) (entries : List Entry) (bits : Nat → Bool)
    (values : ∀ entry∈entries,rho entry.bitColumn=BinaryComparison100.bit (bits entry.bitColumn)) :
    rawScan rho flag entries=BinaryComparison100.scan flag
      (entries.map (fun entry => (bits entry.bitColumn,entry.maximumBit))) := by
  induction entries generalizing flag with
  | nil => rfl
  | cons entry tail ih =>
    change rawScan rho (BinaryComparison100.step flag (rho entry.bitColumn) (BinaryComparison100.bit entry.maximumBit)) tail=
      BinaryComparison100.scan (BinaryComparison100.step flag (BinaryComparison100.bit (bits entry.bitColumn)) (BinaryComparison100.bit entry.maximumBit))
        (tail.map (fun entry => (bits entry.bitColumn,entry.maximumBit)))
    rw [values entry (List.mem_cons_self)]
    exact ih _ (fun entry member => values entry (List.mem_cons_of_mem _ member))
end ShielddSecurity.ComparisonCertificate101
