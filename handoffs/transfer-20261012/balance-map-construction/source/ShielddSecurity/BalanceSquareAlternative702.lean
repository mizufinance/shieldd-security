import Mathlib.RingTheory.IntegralDomain
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.BalanceSquareAlternative702

theorem odd_exponent {F : Type} [Field F] (g : F) (n : Nat) (nonsquare : ¬ IsSquare (g^n)) : n%2=1 := by
  by_contra odd
  have count : n=n/2+n/2 := by omega
  apply nonsquare
  exact ⟨g^(n/2),by rw [← pow_add,← count]⟩

theorem alternative {F : Type} [Field F] [Fintype F] (z value : F)
    (parameter : ¬ IsSquare z) (nonsquare : ¬ IsSquare value) : IsSquare (z*value) := by
  classical
  have zNonzero : z≠0 := by intro zero; exact parameter ⟨0,by simp [zero]⟩
  have nonzero : value≠0 := by intro zero; exact nonsquare ⟨0,by simp [zero]⟩
  let zu : Fˣ := Units.mk0 z zNonzero
  let vu : Fˣ := Units.mk0 value nonzero
  obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α:=Fˣ)
  obtain ⟨n,hn⟩ : zu ∈ Submonoid.powers g := by rw [mem_powers_iff_mem_zpowers]; exact hg zu
  obtain ⟨m,hm⟩ : vu ∈ Submonoid.powers g := by rw [mem_powers_iff_mem_zpowers]; exact hg vu
  have gn : (g:F)^n=z := by
    simpa only [Units.val_pow_eq_pow_val,zu,Units.val_mk0] using congrArg (fun u : Fˣ => (u:F)) hn
  have gm : (g:F)^m=value := by
    simpa only [Units.val_pow_eq_pow_val,vu,Units.val_mk0] using congrArg (fun u : Fˣ => (u:F)) hm
  have nOdd := odd_exponent (g:F) n (by simpa only [gn] using parameter)
  have mOdd := odd_exponent (g:F) m (by simpa only [gm] using nonsquare)
  have count : n+m=(n+m)/2+(n+m)/2 := by omega
  refine ⟨(g:F)^((n+m)/2),?_⟩
  rw [← pow_add,← count,pow_add,gn,gm]
end ShielddSecurity.BalanceSquareAlternative702

set_option pp.all true in
#check @ShielddSecurity.BalanceSquareAlternative702.odd_exponent
#print axioms ShielddSecurity.BalanceSquareAlternative702.odd_exponent
set_option pp.all true in
#check @ShielddSecurity.BalanceSquareAlternative702.alternative
#print axioms ShielddSecurity.BalanceSquareAlternative702.alternative
