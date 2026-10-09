import ShielddSecurity.GroupRowCompletion

set_option maxHeartbeats 150000

namespace ShielddSecurity.GroupQuotientRowSoundness

/-- The three normalized quotient rows enforce multiplication on every
satisfying assignment. Denominator legality is a later curve consequence. -/
theorem product_equation {F : Type} [Field F] (rho : Nat → F)
    (numerator denominator remainder : Linear) (quotient product auxiliary : Nat)
    (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho (GroupRowCompletion.quotientRows numerator denominator
      remainder quotient product auxiliary)) :
    rho quotient * eval rho denominator = eval rho numerator := by
  have minus := satisfied
    ⟨Compiler.subtract [(quotient,1)] denominator,[(auxiliary,1)]⟩
    (List.mem_append_left _ List.mem_cons_self)
  have plus := satisfied
    ⟨[(quotient,1)] ++ denominator,
      [(auxiliary,1)] ++ scaleLinear 4 ([(product,1)] ++ remainder)⟩
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  simp only [Compiler.eval_subtract,eval_append,eval_scale,eval,Int.cast_one,
    one_mul,add_zero,Int.cast_ofNat] at minus plus
  have multiplied := product_encoding (rho quotient) (eval rho denominator)
    (rho auxiliary) (rho product + eval rho remainder) four minus plus
  have boundary := satisfied
    ⟨Compiler.subtract ([(product,1)] ++ remainder) numerator,[]⟩
    (List.mem_append_right _ (List.mem_singleton_self _))
  have zero := square_zero _ boundary
  have same : rho product + eval rho remainder = eval rho numerator := by
    apply sub_eq_zero.mp
    simpa only [Compiler.eval_subtract,eval_append,eval,Int.cast_one,one_mul,add_zero] using zero
  exact multiplied.trans same

set_option pp.all true in
#check @product_equation
#print axioms product_equation

end ShielddSecurity.GroupQuotientRowSoundness
