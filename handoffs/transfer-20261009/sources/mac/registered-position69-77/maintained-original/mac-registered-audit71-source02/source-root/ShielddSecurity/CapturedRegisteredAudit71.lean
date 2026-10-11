import ShielddSecurity.CapturedRegisteredAudit70
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegisteredAudit71
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F] [CharP F p]
theorem actual_primitive (rho : Nat → F) (zero : rho 0=1) (linked : rho copy=rho 0)
    (arithmeticSat : Satisfies rho CapturedRegisteredAudit70.arithmetic)
    (assertionsSat : SatisfiesAt rho CapturedRegisteredAudit70.block.actual 35) :
    CapturedRegisteredAudit70.Primitive rho := by
  have truth:=(satisfies_iff copy 35 CapturedRegisteredAudit70.block rho linked).mp assertionsSat
  intro index bound
  rcases (show index=0 ∨ index=1 ∨ index=2 ∨ index=3 ∨ index=4 ∨ index=5 ∨ index=6 ∨ index=7 ∨ index=8 ∨ index=9 by omega) with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · have a:=truth 0 (by decide) (true,.square [(115,1)] [(115,1)]) rfl
    have b:=truth 1 (by decide) (true,.linear [(23000,1)] [(0,1),(115,-1)]) rfl
    have c:=truth 2 (by decide) (true,.linear [] [(23002,1)]) rfl
    change Square (eval rho [(115,1)]) (eval rho [(115,1)]) at a
    change eval rho [(23000,1)]=eval rho [(0,1),(115,-1)] at b
    change eval rho []=eval rho [(23002,1)] at c
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul] at a b c
    have bPrime : rho 23000=1-rho 115 := by simpa only [zero,sub_eq_add_neg] using b
    have pa:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 0 (by decide)
    have pb:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 1 (by decide)
    change rho 23000=eval rho [(35,1)]*eval rho [(116,1)] at pa
    change rho 23002=eval rho [(35,1)]*eval rho [(115,1)] at pb
    simp only [eval,Int.cast_one,one_mul,add_zero] at pa pb
    change CompilerZeroTest65.Primitive (eval rho [(35,1)]) (rho 115) (rho 116)
    refine ⟨a,?_,?_⟩
    · simpa only [eval,Int.cast_one,one_mul,add_zero] using pa.symm.trans bPrime
    · simpa only [eval,Int.cast_one,one_mul,add_zero] using pb.symm.trans c.symm
  · have a:=truth 3 (by decide) (true,.square [(117,1)] [(117,1)]) rfl
    have b:=truth 4 (by decide) (true,.linear [(23004,1)] [(0,1),(117,-1)]) rfl
    have c:=truth 5 (by decide) (true,.linear [] [(23006,1)]) rfl
    change Square (eval rho [(117,1)]) (eval rho [(117,1)]) at a
    change eval rho [(23004,1)]=eval rho [(0,1),(117,-1)] at b
    change eval rho []=eval rho [(23006,1)] at c
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul] at a b c
    have bPrime : rho 23004=1-rho 117 := by simpa only [zero,sub_eq_add_neg] using b
    have pa:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 2 (by decide)
    have pb:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 3 (by decide)
    change rho 23004=eval rho [(0,-1),(36,1)]*eval rho [(118,1)] at pa
    change rho 23006=eval rho [(0,-1),(36,1)]*eval rho [(117,1)] at pb
    simp only [eval,Int.cast_one,one_mul,add_zero] at pa pb
    change CompilerZeroTest65.Primitive (eval rho [(0,-1),(36,1)]) (rho 117) (rho 118)
    refine ⟨a,?_,?_⟩
    · simpa only [eval,Int.cast_one,one_mul,add_zero] using pa.symm.trans bPrime
    · simpa only [eval,Int.cast_one,one_mul,add_zero] using pb.symm.trans c.symm
  · have a:=truth 7 (by decide) (true,.square [(119,1)] [(119,1)]) rfl
    have b:=truth 8 (by decide) (true,.linear [(23012,1)] [(0,1),(119,-1)]) rfl
    have c:=truth 9 (by decide) (true,.linear [] [(23014,1)]) rfl
    change Square (eval rho [(119,1)]) (eval rho [(119,1)]) at a
    change eval rho [(23012,1)]=eval rho [(0,1),(119,-1)] at b
    change eval rho []=eval rho [(23014,1)] at c
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul] at a b c
    have bPrime : rho 23012=1-rho 119 := by simpa only [zero,sub_eq_add_neg] using b
    have pa:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 6 (by decide)
    have pb:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 7 (by decide)
    change rho 23012=eval rho [(0,2613035198500699080012737903016384954916552590968062488514021062113153911183),(35,1)]*eval rho [(120,1)] at pa
    change rho 23014=eval rho [(0,2613035198500699080012737903016384954916552590968062488514021062113153911183),(35,1)]*eval rho [(119,1)] at pb
    simp only [eval,Int.cast_one,one_mul,add_zero] at pa pb
    change CompilerZeroTest65.Primitive (eval rho [(0,2613035198500699080012737903016384954916552590968062488514021062113153911183),(35,1)]) (rho 119) (rho 120)
    refine ⟨a,?_,?_⟩
    · simpa only [eval,Int.cast_one,one_mul,add_zero] using pa.symm.trans bPrime
    · simpa only [eval,Int.cast_one,one_mul,add_zero] using pb.symm.trans c.symm
  · have a:=truth 10 (by decide) (true,.square [(121,1)] [(121,1)]) rfl
    have b:=truth 11 (by decide) (true,.linear [(23016,1)] [(0,1),(121,-1)]) rfl
    have c:=truth 12 (by decide) (true,.linear [] [(23018,1)]) rfl
    change Square (eval rho [(121,1)]) (eval rho [(121,1)]) at a
    change eval rho [(23016,1)]=eval rho [(0,1),(121,-1)] at b
    change eval rho []=eval rho [(23018,1)] at c
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul] at a b c
    have bPrime : rho 23016=1-rho 121 := by simpa only [zero,sub_eq_add_neg] using b
    have pa:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 8 (by decide)
    have pb:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 9 (by decide)
    change rho 23016=eval rho [(0,23326889571876200994796012627856472314977644248009733575144307806885254871463),(36,1)]*eval rho [(122,1)] at pa
    change rho 23018=eval rho [(0,23326889571876200994796012627856472314977644248009733575144307806885254871463),(36,1)]*eval rho [(121,1)] at pb
    simp only [eval,Int.cast_one,one_mul,add_zero] at pa pb
    change CompilerZeroTest65.Primitive (eval rho [(0,23326889571876200994796012627856472314977644248009733575144307806885254871463),(36,1)]) (rho 121) (rho 122)
    refine ⟨a,?_,?_⟩
    · simpa only [eval,Int.cast_one,one_mul,add_zero] using pa.symm.trans bPrime
    · simpa only [eval,Int.cast_one,one_mul,add_zero] using pb.symm.trans c.symm
  · have a:=truth 14 (by decide) (true,.square [(123,1)] [(123,1)]) rfl
    have b:=truth 15 (by decide) (true,.linear [(23024,1)] [(0,1),(123,-1)]) rfl
    have c:=truth 16 (by decide) (true,.linear [] [(23026,1)]) rfl
    change Square (eval rho [(123,1)]) (eval rho [(123,1)]) at a
    change eval rho [(23024,1)]=eval rho [(0,1),(123,-1)] at b
    change eval rho []=eval rho [(23026,1)] at c
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul] at a b c
    have bPrime : rho 23024=1-rho 123 := by simpa only [zero,sub_eq_add_neg] using b
    have pa:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 12 (by decide)
    have pb:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 13 (by decide)
    change rho 23024=eval rho [(35,1),(42,-1)]*eval rho [(124,1)] at pa
    change rho 23026=eval rho [(35,1),(42,-1)]*eval rho [(123,1)] at pb
    simp only [eval,Int.cast_one,one_mul,add_zero] at pa pb
    change CompilerZeroTest65.Primitive (eval rho [(35,1),(42,-1)]) (rho 123) (rho 124)
    refine ⟨a,?_,?_⟩
    · simpa only [eval,Int.cast_one,one_mul,add_zero] using pa.symm.trans bPrime
    · simpa only [eval,Int.cast_one,one_mul,add_zero] using pb.symm.trans c.symm
  · have a:=truth 17 (by decide) (true,.square [(125,1)] [(125,1)]) rfl
    have b:=truth 18 (by decide) (true,.linear [(23028,1)] [(0,1),(125,-1)]) rfl
    have c:=truth 19 (by decide) (true,.linear [] [(23030,1)]) rfl
    change Square (eval rho [(125,1)]) (eval rho [(125,1)]) at a
    change eval rho [(23028,1)]=eval rho [(0,1),(125,-1)] at b
    change eval rho []=eval rho [(23030,1)] at c
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul] at a b c
    have bPrime : rho 23028=1-rho 125 := by simpa only [zero,sub_eq_add_neg] using b
    have pa:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 14 (by decide)
    have pb:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 15 (by decide)
    change rho 23028=eval rho [(36,1),(43,-1)]*eval rho [(126,1)] at pa
    change rho 23030=eval rho [(36,1),(43,-1)]*eval rho [(125,1)] at pb
    simp only [eval,Int.cast_one,one_mul,add_zero] at pa pb
    change CompilerZeroTest65.Primitive (eval rho [(36,1),(43,-1)]) (rho 125) (rho 126)
    refine ⟨a,?_,?_⟩
    · simpa only [eval,Int.cast_one,one_mul,add_zero] using pa.symm.trans bPrime
    · simpa only [eval,Int.cast_one,one_mul,add_zero] using pb.symm.trans c.symm
  · have a:=truth 21 (by decide) (true,.square [(127,1)] [(127,1)]) rfl
    have b:=truth 22 (by decide) (true,.linear [(23036,1)] [(0,1),(127,-1)]) rfl
    have c:=truth 23 (by decide) (true,.linear [] [(23038,1)]) rfl
    change Square (eval rho [(127,1)]) (eval rho [(127,1)]) at a
    change eval rho [(23036,1)]=eval rho [(0,1),(127,-1)] at b
    change eval rho []=eval rho [(23038,1)] at c
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul] at a b c
    have bPrime : rho 23036=1-rho 127 := by simpa only [zero,sub_eq_add_neg] using b
    have pa:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 18 (by decide)
    have pb:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 19 (by decide)
    change rho 23036=eval rho [(42,1)]*eval rho [(128,1)] at pa
    change rho 23038=eval rho [(42,1)]*eval rho [(127,1)] at pb
    simp only [eval,Int.cast_one,one_mul,add_zero] at pa pb
    change CompilerZeroTest65.Primitive (eval rho [(42,1)]) (rho 127) (rho 128)
    refine ⟨a,?_,?_⟩
    · simpa only [eval,Int.cast_one,one_mul,add_zero] using pa.symm.trans bPrime
    · simpa only [eval,Int.cast_one,one_mul,add_zero] using pb.symm.trans c.symm
  · have a:=truth 24 (by decide) (true,.square [(129,1)] [(129,1)]) rfl
    have b:=truth 25 (by decide) (true,.linear [(23040,1)] [(0,1),(129,-1)]) rfl
    have c:=truth 26 (by decide) (true,.linear [] [(23042,1)]) rfl
    change Square (eval rho [(129,1)]) (eval rho [(129,1)]) at a
    change eval rho [(23040,1)]=eval rho [(0,1),(129,-1)] at b
    change eval rho []=eval rho [(23042,1)] at c
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul] at a b c
    have bPrime : rho 23040=1-rho 129 := by simpa only [zero,sub_eq_add_neg] using b
    have pa:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 20 (by decide)
    have pb:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 21 (by decide)
    change rho 23040=eval rho [(0,-1),(43,1)]*eval rho [(130,1)] at pa
    change rho 23042=eval rho [(0,-1),(43,1)]*eval rho [(129,1)] at pb
    simp only [eval,Int.cast_one,one_mul,add_zero] at pa pb
    change CompilerZeroTest65.Primitive (eval rho [(0,-1),(43,1)]) (rho 129) (rho 130)
    refine ⟨a,?_,?_⟩
    · simpa only [eval,Int.cast_one,one_mul,add_zero] using pa.symm.trans bPrime
    · simpa only [eval,Int.cast_one,one_mul,add_zero] using pb.symm.trans c.symm
  · have a:=truth 28 (by decide) (true,.square [(131,1)] [(131,1)]) rfl
    have b:=truth 29 (by decide) (true,.linear [(23048,1)] [(0,1),(131,-1)]) rfl
    have c:=truth 30 (by decide) (true,.linear [] [(23050,1)]) rfl
    change Square (eval rho [(131,1)]) (eval rho [(131,1)]) at a
    change eval rho [(23048,1)]=eval rho [(0,1),(131,-1)] at b
    change eval rho []=eval rho [(23050,1)] at c
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul] at a b c
    have bPrime : rho 23048=1-rho 131 := by simpa only [zero,sub_eq_add_neg] using b
    have pa:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 24 (by decide)
    have pb:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 25 (by decide)
    change rho 23048=eval rho [(0,2613035198500699080012737903016384954916552590968062488514021062113153911183),(42,1)]*eval rho [(132,1)] at pa
    change rho 23050=eval rho [(0,2613035198500699080012737903016384954916552590968062488514021062113153911183),(42,1)]*eval rho [(131,1)] at pb
    simp only [eval,Int.cast_one,one_mul,add_zero] at pa pb
    change CompilerZeroTest65.Primitive (eval rho [(0,2613035198500699080012737903016384954916552590968062488514021062113153911183),(42,1)]) (rho 131) (rho 132)
    refine ⟨a,?_,?_⟩
    · simpa only [eval,Int.cast_one,one_mul,add_zero] using pa.symm.trans bPrime
    · simpa only [eval,Int.cast_one,one_mul,add_zero] using pb.symm.trans c.symm
  · have a:=truth 31 (by decide) (true,.square [(133,1)] [(133,1)]) rfl
    have b:=truth 32 (by decide) (true,.linear [(23052,1)] [(0,1),(133,-1)]) rfl
    have c:=truth 33 (by decide) (true,.linear [] [(23054,1)]) rfl
    change Square (eval rho [(133,1)]) (eval rho [(133,1)]) at a
    change eval rho [(23052,1)]=eval rho [(0,1),(133,-1)] at b
    change eval rho []=eval rho [(23054,1)] at c
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul] at a b c
    have bPrime : rho 23052=1-rho 133 := by simpa only [zero,sub_eq_add_neg] using b
    have pa:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 26 (by decide)
    have pb:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 27 (by decide)
    change rho 23052=eval rho [(0,23326889571876200994796012627856472314977644248009733575144307806885254871463),(43,1)]*eval rho [(134,1)] at pa
    change rho 23054=eval rho [(0,23326889571876200994796012627856472314977644248009733575144307806885254871463),(43,1)]*eval rho [(133,1)] at pb
    simp only [eval,Int.cast_one,one_mul,add_zero] at pa pb
    change CompilerZeroTest65.Primitive (eval rho [(0,23326889571876200994796012627856472314977644248009733575144307806885254871463),(43,1)]) (rho 133) (rho 134)
    refine ⟨a,?_,?_⟩
    · simpa only [eval,Int.cast_one,one_mul,add_zero] using pa.symm.trans bPrime
    · simpa only [eval,Int.cast_one,one_mul,add_zero] using pb.symm.trans c.symm
def Guards (rho : Nat → F) : Prop := ∀ pair<5,
  rho 10*(rho (115+4*pair)*rho (117+4*pair))=0
theorem actual_guards (rho : Nat → F) (linked : rho copy=rho 0)
    (arithmeticSat : Satisfies rho CapturedRegisteredAudit70.arithmetic)
    (assertionsSat : SatisfiesAt rho CapturedRegisteredAudit70.block.actual 35) : Guards rho := by
  have truth:=(satisfies_iff copy 35 CapturedRegisteredAudit70.block rho linked).mp assertionsSat
  intro pair bound
  rcases (show pair=0 ∨ pair=1 ∨ pair=2 ∨ pair=3 ∨ pair=4 by omega) with rfl|rfl|rfl|rfl|rfl
  · have a:=truth 6 (by decide) (true,.linear [] [(23010,1)]) rfl
    change eval rho []=eval rho [(23010,1)] at a
    simp only [eval,Int.cast_one,one_mul,add_zero] at a
    have b:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 4 (by decide)
    have c:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 5 (by decide)
    change rho 23008=eval rho [(115,1)]*eval rho [(117,1)] at b
    change rho 23010=eval rho [(10,1)]*eval rho [(23008,1)] at c
    simp only [eval,Int.cast_one,one_mul,add_zero] at b c
    change rho 10*(rho 115*rho 117)=0
    exact (congrArg (fun value => rho 10*value) b).symm.trans (c.symm.trans a.symm)
  · have a:=truth 13 (by decide) (true,.linear [] [(23022,1)]) rfl
    change eval rho []=eval rho [(23022,1)] at a
    simp only [eval,Int.cast_one,one_mul,add_zero] at a
    have b:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 10 (by decide)
    have c:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 11 (by decide)
    change rho 23020=eval rho [(119,1)]*eval rho [(121,1)] at b
    change rho 23022=eval rho [(10,1)]*eval rho [(23020,1)] at c
    simp only [eval,Int.cast_one,one_mul,add_zero] at b c
    change rho 10*(rho 119*rho 121)=0
    exact (congrArg (fun value => rho 10*value) b).symm.trans (c.symm.trans a.symm)
  · have a:=truth 20 (by decide) (true,.linear [] [(23034,1)]) rfl
    change eval rho []=eval rho [(23034,1)] at a
    simp only [eval,Int.cast_one,one_mul,add_zero] at a
    have b:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 16 (by decide)
    have c:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 17 (by decide)
    change rho 23032=eval rho [(123,1)]*eval rho [(125,1)] at b
    change rho 23034=eval rho [(10,1)]*eval rho [(23032,1)] at c
    simp only [eval,Int.cast_one,one_mul,add_zero] at b c
    change rho 10*(rho 123*rho 125)=0
    exact (congrArg (fun value => rho 10*value) b).symm.trans (c.symm.trans a.symm)
  · have a:=truth 27 (by decide) (true,.linear [] [(23046,1)]) rfl
    change eval rho []=eval rho [(23046,1)] at a
    simp only [eval,Int.cast_one,one_mul,add_zero] at a
    have b:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 22 (by decide)
    have c:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 23 (by decide)
    change rho 23044=eval rho [(127,1)]*eval rho [(129,1)] at b
    change rho 23046=eval rho [(10,1)]*eval rho [(23044,1)] at c
    simp only [eval,Int.cast_one,one_mul,add_zero] at b c
    change rho 10*(rho 127*rho 129)=0
    exact (congrArg (fun value => rho 10*value) b).symm.trans (c.symm.trans a.symm)
  · have a:=truth 34 (by decide) (true,.linear [] [(23058,1)]) rfl
    change eval rho []=eval rho [(23058,1)] at a
    simp only [eval,Int.cast_one,one_mul,add_zero] at a
    have b:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 28 (by decide)
    have c:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 29 (by decide)
    change rho 23056=eval rho [(131,1)]*eval rho [(133,1)] at b
    change rho 23058=eval rho [(10,1)]*eval rho [(23056,1)] at c
    simp only [eval,Int.cast_one,one_mul,add_zero] at b c
    change rho 10*(rho 131*rho 133)=0
    exact (congrArg (fun value => rho 10*value) b).symm.trans (c.symm.trans a.symm)
theorem forbidden_pair (rho : Nat → F) (zero : rho 0=1) (linked : rho copy=rho 0)
    (arithmeticSat : Satisfies rho CapturedRegisteredAudit70.arithmetic)
    (assertionsSat : SatisfiesAt rho CapturedRegisteredAudit70.block.actual 35)
    (pair : Nat) (bound : pair<5) :
    eval rho (CapturedRegisteredAudit70.zeroTerms (2*pair))=0 ∧
    eval rho (CapturedRegisteredAudit70.zeroTerms (2*pair+1))=0 → rho 10=0 := by
  have primitive:=actual_primitive rho zero linked arithmeticSat assertionsSat
  have guards:=actual_guards rho linked arithmeticSat assertionsSat
  have left:=primitive (2*pair) (by omega)
  have right:=primitive (2*pair+1) (by omega)
  have checked:=CompilerCoordinateZero69.guard_iff
    (eval rho (CapturedRegisteredAudit70.zeroTerms (2*pair)))
    (eval rho (CapturedRegisteredAudit70.zeroTerms (2*pair+1)))
    (rho (115+2*(2*pair))) (rho (116+2*(2*pair)))
    (rho (115+2*(2*pair+1))) (rho (116+2*(2*pair+1))) (rho 10) ⟨left,right⟩
  apply checked.mp
  convert guards pair bound using 1 <;> congr 2 <;> omega
end ShielddSecurity.CapturedRegisteredAudit71

set_option pp.all true in
#check @ShielddSecurity.CapturedRegisteredAudit71.actual_primitive
#print axioms ShielddSecurity.CapturedRegisteredAudit71.actual_primitive
set_option pp.all true in
#check @ShielddSecurity.CapturedRegisteredAudit71.Guards
#print axioms ShielddSecurity.CapturedRegisteredAudit71.Guards
set_option pp.all true in
#check @ShielddSecurity.CapturedRegisteredAudit71.actual_guards
#print axioms ShielddSecurity.CapturedRegisteredAudit71.actual_guards
set_option pp.all true in
#check @ShielddSecurity.CapturedRegisteredAudit71.forbidden_pair
#print axioms ShielddSecurity.CapturedRegisteredAudit71.forbidden_pair
