import ShielddSecurity.CompilerAssertionBlock51
import ShielddSecurity.CompilerArithmeticTransport41
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CompilerVerifierLinks53
open CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F] [CharP F p]
theorem checked_unoutlined_iff (actual : Row) (recipe : CompilerAssertionBlock51.Recipe)
    (checked : checkRow p copy actual (false,recipe)=true) (rho : Nat → F) :
    Square (eval rho actual.a) (eval rho actual.b) ↔ Truth rho recipe := by
  have h:=of_decide_eq_true checked
  have left:=Compiler.canonical_equal rho actual.a (expected recipe).a h.1
  have right:=Compiler.canonical_equal rho actual.b (expected recipe).b h.2
  rw [left,right]
  exact expected_iff rho recipe

def linkRow (left right : Nat) : Row := ⟨[(left,1),(right,Int.ofNat (p-1))],[]⟩
theorem residue_cast : ((Int.ofNat (p-1)) : F) = -1 := by
  have positive : 1 ≤ p := by decide
  have zero : (p : F) = 0 := (CharP.cast_eq_zero_iff F p p).mpr (dvd_refl p)
  rw [Int.ofNat_eq_natCast,Int.cast_natCast,Nat.cast_sub positive,Nat.cast_one,zero,zero_sub]
theorem link_iff (rho : Nat → F) (left right : Nat) :
    Square (eval rho (linkRow left right).a) (eval rho (linkRow left right).b) ↔ rho left=rho right := by
  simp only [linkRow,eval,Int.cast_one,residue_cast,one_mul,neg_one_mul,add_zero]
  rw [←sub_eq_add_neg]
  constructor
  · intro sat
    exact sub_eq_zero.mp (Compiler.square_zero _ sat)
  · intro same
    rw [same,sub_self]
    simp [Square]

omit [Field F] [CharP F p] in
noncomputable def seeded (base : Nat → F) (column : Nat) : F :=
  if column=copy then base 0 else if column=1 then base 22737 else if column=2 then base 9 else base column
omit [Field F] [CharP F p] in
theorem seeded_outside (base : Nat → F) (column : Nat)
    (different : column≠copy ∧ column≠1 ∧ column≠2) : seeded base column=base column := by
  simp only [seeded,different.1,different.2.1,different.2.2,if_false]
omit [Field F] [CharP F p] in
theorem seeded_original_inputs (base : Nat → F) (input : Nat) (bound : input<22735) :
    seeded base (3+input)=base (3+input) := by
  apply seeded_outside
  change 3+input≠200692 ∧ 3+input≠1 ∧ 3+input≠2
  omega
omit [Field F] [CharP F p] in
theorem seeded_zero (base : Nat → F) : seeded base 0=base 0 := by
  apply seeded_outside
  decide
omit [Field F] [CharP F p] in
theorem seeded_copy (base : Nat → F) : seeded base copy=seeded base 0 := by
  rw [seeded_zero]
  simp only [seeded,if_true]
omit [Field F] [CharP F p] in
theorem seeded_public (base : Nat → F) : seeded base 1=seeded base 22737 := by
  have unchanged : seeded base 22737=base 22737:=seeded_original_inputs base 22734 (by decide)
  rw [unchanged]
  simp [seeded,copy]
omit [Field F] [CharP F p] in
theorem seeded_committed (base : Nat → F) : seeded base 2=seeded base 9 := by
  have unchanged : seeded base 9=base 9:=seeded_original_inputs base 6 (by decide)
  rw [unchanged]
  simp [seeded,copy]
theorem seeded_links (base : Nat → F) :
    Square (eval (seeded base) (linkRow 1 22737).a) (eval (seeded base) (linkRow 1 22737).b) ∧
    Square (eval (seeded base) (linkRow 2 9).a) (eval (seeded base) (linkRow 2 9).b) ∧
    Square (eval (seeded base) (linkRow 0 copy).a) (eval (seeded base) (linkRow 0 copy).b) := by
  exact ⟨(link_iff (seeded base) 1 22737).mpr (seeded_public base),
    (link_iff (seeded base) 2 9).mpr (seeded_committed base),
    (link_iff (seeded base) 0 copy).mpr (seeded_copy base).symm⟩
end ShielddSecurity.CompilerVerifierLinks53

set_option pp.all true in
#check @ShielddSecurity.CompilerVerifierLinks53.checked_unoutlined_iff
#print axioms ShielddSecurity.CompilerVerifierLinks53.checked_unoutlined_iff
set_option pp.all true in
#check @ShielddSecurity.CompilerVerifierLinks53.linkRow
#print axioms ShielddSecurity.CompilerVerifierLinks53.linkRow
set_option pp.all true in
#check @ShielddSecurity.CompilerVerifierLinks53.residue_cast
#print axioms ShielddSecurity.CompilerVerifierLinks53.residue_cast
set_option pp.all true in
#check @ShielddSecurity.CompilerVerifierLinks53.link_iff
#print axioms ShielddSecurity.CompilerVerifierLinks53.link_iff
set_option pp.all true in
#check @ShielddSecurity.CompilerVerifierLinks53.seeded
#print axioms ShielddSecurity.CompilerVerifierLinks53.seeded
set_option pp.all true in
#check @ShielddSecurity.CompilerVerifierLinks53.seeded_outside
#print axioms ShielddSecurity.CompilerVerifierLinks53.seeded_outside
set_option pp.all true in
#check @ShielddSecurity.CompilerVerifierLinks53.seeded_original_inputs
#print axioms ShielddSecurity.CompilerVerifierLinks53.seeded_original_inputs
set_option pp.all true in
#check @ShielddSecurity.CompilerVerifierLinks53.seeded_zero
#print axioms ShielddSecurity.CompilerVerifierLinks53.seeded_zero
set_option pp.all true in
#check @ShielddSecurity.CompilerVerifierLinks53.seeded_copy
#print axioms ShielddSecurity.CompilerVerifierLinks53.seeded_copy
set_option pp.all true in
#check @ShielddSecurity.CompilerVerifierLinks53.seeded_public
#print axioms ShielddSecurity.CompilerVerifierLinks53.seeded_public
set_option pp.all true in
#check @ShielddSecurity.CompilerVerifierLinks53.seeded_committed
#print axioms ShielddSecurity.CompilerVerifierLinks53.seeded_committed
set_option pp.all true in
#check @ShielddSecurity.CompilerVerifierLinks53.seeded_links
#print axioms ShielddSecurity.CompilerVerifierLinks53.seeded_links
