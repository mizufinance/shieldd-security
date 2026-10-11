import ShielddSecurity.CapturedRegisteredAudit71
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegisteredAssertions73
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F] [CharP F p]
theorem primitive_assertions (rho : Nat → F) (zero : rho 0=1) (linked : rho copy=rho 0)
    (arithmeticSat : Satisfies rho CapturedRegisteredAudit70.arithmetic)
    (primitive : CapturedRegisteredAudit70.Primitive rho)
    (guards : CapturedRegisteredAudit71.Guards rho) :
    SatisfiesAt rho CapturedRegisteredAudit70.block.actual 35 := by
  apply (satisfies_iff copy 35 CapturedRegisteredAudit70.block rho linked).mpr
  intro index bound hint found
  rcases (show index=0 ∨ index=1 ∨ index=2 ∨ index=3 ∨ index=4 ∨ index=5 ∨ index=6 ∨ index=7 ∨ index=8 ∨ index=9 ∨ index=10 ∨ index=11 ∨ index=12 ∨ index=13 ∨ index=14 ∨ index=15 ∨ index=16 ∨ index=17 ∨ index=18 ∨ index=19 ∨ index=20 ∨ index=21 ∨ index=22 ∨ index=23 ∨ index=24 ∨ index=25 ∨ index=26 ∨ index=27 ∨ index=28 ∨ index=29 ∨ index=30 ∨ index=31 ∨ index=32 ∨ index=33 ∨ index=34 by omega) with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · change some (true,.square [(115,1)] [(115,1)])=some hint at found
    cases found
    have h:=primitive 0 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(35,1)]) (rho 115) (rho 116) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    change Square (eval rho [(115,1)]) (eval rho [(115,1)])
    simpa only [eval,Int.cast_one,one_mul,add_zero] using h.1
  · change some (true,.linear [(23000,1)] [(0,1),(115,-1)])=some hint at found
    cases found
    have h:=primitive 0 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(35,1)]) (rho 115) (rho 116) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    have pa:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 0 (by decide)
    change rho 23000=eval rho [(35,1)]*eval rho [(116,1)] at pa
    simp only [eval,Int.cast_one,one_mul,add_zero] at pa
    change eval rho [(23000,1)]=eval rho [(0,1),(115,-1)]
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul,zero]
    simpa only [eval,Int.cast_one,one_mul,add_zero,sub_eq_add_neg] using pa.trans h.2.1
  · change some (true,.linear [] [(23002,1)])=some hint at found
    cases found
    have h:=primitive 0 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(35,1)]) (rho 115) (rho 116) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    have pb:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 1 (by decide)
    change rho 23002=eval rho [(35,1)]*eval rho [(115,1)] at pb
    simp only [eval,Int.cast_one,one_mul,add_zero] at pb
    change eval rho []=eval rho [(23002,1)]
    simpa only [eval,Int.cast_one,one_mul,add_zero] using (pb.trans h.2.2).symm
  · change some (true,.square [(117,1)] [(117,1)])=some hint at found
    cases found
    have h:=primitive 1 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(0,-1),(36,1)]) (rho 117) (rho 118) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    change Square (eval rho [(117,1)]) (eval rho [(117,1)])
    simpa only [eval,Int.cast_one,one_mul,add_zero] using h.1
  · change some (true,.linear [(23004,1)] [(0,1),(117,-1)])=some hint at found
    cases found
    have h:=primitive 1 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(0,-1),(36,1)]) (rho 117) (rho 118) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    have pa:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 2 (by decide)
    change rho 23004=eval rho [(0,-1),(36,1)]*eval rho [(118,1)] at pa
    simp only [eval,Int.cast_one,one_mul,add_zero] at pa
    change eval rho [(23004,1)]=eval rho [(0,1),(117,-1)]
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul,zero]
    simpa only [eval,Int.cast_one,one_mul,add_zero,sub_eq_add_neg] using pa.trans h.2.1
  · change some (true,.linear [] [(23006,1)])=some hint at found
    cases found
    have h:=primitive 1 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(0,-1),(36,1)]) (rho 117) (rho 118) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    have pb:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 3 (by decide)
    change rho 23006=eval rho [(0,-1),(36,1)]*eval rho [(117,1)] at pb
    simp only [eval,Int.cast_one,one_mul,add_zero] at pb
    change eval rho []=eval rho [(23006,1)]
    simpa only [eval,Int.cast_one,one_mul,add_zero] using (pb.trans h.2.2).symm
  · change some (true,.linear [] [(23010,1)])=some hint at found
    cases found
    have b:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 4 (by decide)
    have c:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 5 (by decide)
    change rho 23008=eval rho [(115,1)]*eval rho [(117,1)] at b
    change rho 23010=eval rho [(10,1)]*eval rho [(23008,1)] at c
    simp only [eval,Int.cast_one,one_mul,add_zero] at b c
    change eval rho []=eval rho [(23010,1)]
    have g:=guards 0 (by decide)
    change rho 10*(rho 115*rho 117)=0 at g
    simpa only [eval,Int.cast_one,one_mul,add_zero] using (c.trans ((congrArg (fun value => rho 10*value) b).trans g)).symm
  · change some (true,.square [(119,1)] [(119,1)])=some hint at found
    cases found
    have h:=primitive 2 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(0,2613035198500699080012737903016384954916552590968062488514021062113153911183),(35,1)]) (rho 119) (rho 120) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    change Square (eval rho [(119,1)]) (eval rho [(119,1)])
    simpa only [eval,Int.cast_one,one_mul,add_zero] using h.1
  · change some (true,.linear [(23012,1)] [(0,1),(119,-1)])=some hint at found
    cases found
    have h:=primitive 2 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(0,2613035198500699080012737903016384954916552590968062488514021062113153911183),(35,1)]) (rho 119) (rho 120) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    have pa:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 6 (by decide)
    change rho 23012=eval rho [(0,2613035198500699080012737903016384954916552590968062488514021062113153911183),(35,1)]*eval rho [(120,1)] at pa
    simp only [eval,Int.cast_one,one_mul,add_zero] at pa
    change eval rho [(23012,1)]=eval rho [(0,1),(119,-1)]
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul,zero]
    simpa only [eval,Int.cast_one,one_mul,add_zero,sub_eq_add_neg] using pa.trans h.2.1
  · change some (true,.linear [] [(23014,1)])=some hint at found
    cases found
    have h:=primitive 2 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(0,2613035198500699080012737903016384954916552590968062488514021062113153911183),(35,1)]) (rho 119) (rho 120) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    have pb:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 7 (by decide)
    change rho 23014=eval rho [(0,2613035198500699080012737903016384954916552590968062488514021062113153911183),(35,1)]*eval rho [(119,1)] at pb
    simp only [eval,Int.cast_one,one_mul,add_zero] at pb
    change eval rho []=eval rho [(23014,1)]
    simpa only [eval,Int.cast_one,one_mul,add_zero] using (pb.trans h.2.2).symm
  · change some (true,.square [(121,1)] [(121,1)])=some hint at found
    cases found
    have h:=primitive 3 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(0,23326889571876200994796012627856472314977644248009733575144307806885254871463),(36,1)]) (rho 121) (rho 122) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    change Square (eval rho [(121,1)]) (eval rho [(121,1)])
    simpa only [eval,Int.cast_one,one_mul,add_zero] using h.1
  · change some (true,.linear [(23016,1)] [(0,1),(121,-1)])=some hint at found
    cases found
    have h:=primitive 3 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(0,23326889571876200994796012627856472314977644248009733575144307806885254871463),(36,1)]) (rho 121) (rho 122) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    have pa:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 8 (by decide)
    change rho 23016=eval rho [(0,23326889571876200994796012627856472314977644248009733575144307806885254871463),(36,1)]*eval rho [(122,1)] at pa
    simp only [eval,Int.cast_one,one_mul,add_zero] at pa
    change eval rho [(23016,1)]=eval rho [(0,1),(121,-1)]
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul,zero]
    simpa only [eval,Int.cast_one,one_mul,add_zero,sub_eq_add_neg] using pa.trans h.2.1
  · change some (true,.linear [] [(23018,1)])=some hint at found
    cases found
    have h:=primitive 3 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(0,23326889571876200994796012627856472314977644248009733575144307806885254871463),(36,1)]) (rho 121) (rho 122) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    have pb:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 9 (by decide)
    change rho 23018=eval rho [(0,23326889571876200994796012627856472314977644248009733575144307806885254871463),(36,1)]*eval rho [(121,1)] at pb
    simp only [eval,Int.cast_one,one_mul,add_zero] at pb
    change eval rho []=eval rho [(23018,1)]
    simpa only [eval,Int.cast_one,one_mul,add_zero] using (pb.trans h.2.2).symm
  · change some (true,.linear [] [(23022,1)])=some hint at found
    cases found
    have b:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 10 (by decide)
    have c:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 11 (by decide)
    change rho 23020=eval rho [(119,1)]*eval rho [(121,1)] at b
    change rho 23022=eval rho [(10,1)]*eval rho [(23020,1)] at c
    simp only [eval,Int.cast_one,one_mul,add_zero] at b c
    change eval rho []=eval rho [(23022,1)]
    have g:=guards 1 (by decide)
    change rho 10*(rho 119*rho 121)=0 at g
    simpa only [eval,Int.cast_one,one_mul,add_zero] using (c.trans ((congrArg (fun value => rho 10*value) b).trans g)).symm
  · change some (true,.square [(123,1)] [(123,1)])=some hint at found
    cases found
    have h:=primitive 4 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(35,1),(42,-1)]) (rho 123) (rho 124) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    change Square (eval rho [(123,1)]) (eval rho [(123,1)])
    simpa only [eval,Int.cast_one,one_mul,add_zero] using h.1
  · change some (true,.linear [(23024,1)] [(0,1),(123,-1)])=some hint at found
    cases found
    have h:=primitive 4 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(35,1),(42,-1)]) (rho 123) (rho 124) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    have pa:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 12 (by decide)
    change rho 23024=eval rho [(35,1),(42,-1)]*eval rho [(124,1)] at pa
    simp only [eval,Int.cast_one,one_mul,add_zero] at pa
    change eval rho [(23024,1)]=eval rho [(0,1),(123,-1)]
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul,zero]
    simpa only [eval,Int.cast_one,one_mul,add_zero,sub_eq_add_neg] using pa.trans h.2.1
  · change some (true,.linear [] [(23026,1)])=some hint at found
    cases found
    have h:=primitive 4 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(35,1),(42,-1)]) (rho 123) (rho 124) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    have pb:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 13 (by decide)
    change rho 23026=eval rho [(35,1),(42,-1)]*eval rho [(123,1)] at pb
    simp only [eval,Int.cast_one,one_mul,add_zero] at pb
    change eval rho []=eval rho [(23026,1)]
    simpa only [eval,Int.cast_one,one_mul,add_zero] using (pb.trans h.2.2).symm
  · change some (true,.square [(125,1)] [(125,1)])=some hint at found
    cases found
    have h:=primitive 5 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(36,1),(43,-1)]) (rho 125) (rho 126) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    change Square (eval rho [(125,1)]) (eval rho [(125,1)])
    simpa only [eval,Int.cast_one,one_mul,add_zero] using h.1
  · change some (true,.linear [(23028,1)] [(0,1),(125,-1)])=some hint at found
    cases found
    have h:=primitive 5 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(36,1),(43,-1)]) (rho 125) (rho 126) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    have pa:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 14 (by decide)
    change rho 23028=eval rho [(36,1),(43,-1)]*eval rho [(126,1)] at pa
    simp only [eval,Int.cast_one,one_mul,add_zero] at pa
    change eval rho [(23028,1)]=eval rho [(0,1),(125,-1)]
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul,zero]
    simpa only [eval,Int.cast_one,one_mul,add_zero,sub_eq_add_neg] using pa.trans h.2.1
  · change some (true,.linear [] [(23030,1)])=some hint at found
    cases found
    have h:=primitive 5 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(36,1),(43,-1)]) (rho 125) (rho 126) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    have pb:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 15 (by decide)
    change rho 23030=eval rho [(36,1),(43,-1)]*eval rho [(125,1)] at pb
    simp only [eval,Int.cast_one,one_mul,add_zero] at pb
    change eval rho []=eval rho [(23030,1)]
    simpa only [eval,Int.cast_one,one_mul,add_zero] using (pb.trans h.2.2).symm
  · change some (true,.linear [] [(23034,1)])=some hint at found
    cases found
    have b:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 16 (by decide)
    have c:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 17 (by decide)
    change rho 23032=eval rho [(123,1)]*eval rho [(125,1)] at b
    change rho 23034=eval rho [(10,1)]*eval rho [(23032,1)] at c
    simp only [eval,Int.cast_one,one_mul,add_zero] at b c
    change eval rho []=eval rho [(23034,1)]
    have g:=guards 2 (by decide)
    change rho 10*(rho 123*rho 125)=0 at g
    simpa only [eval,Int.cast_one,one_mul,add_zero] using (c.trans ((congrArg (fun value => rho 10*value) b).trans g)).symm
  · change some (true,.square [(127,1)] [(127,1)])=some hint at found
    cases found
    have h:=primitive 6 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(42,1)]) (rho 127) (rho 128) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    change Square (eval rho [(127,1)]) (eval rho [(127,1)])
    simpa only [eval,Int.cast_one,one_mul,add_zero] using h.1
  · change some (true,.linear [(23036,1)] [(0,1),(127,-1)])=some hint at found
    cases found
    have h:=primitive 6 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(42,1)]) (rho 127) (rho 128) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    have pa:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 18 (by decide)
    change rho 23036=eval rho [(42,1)]*eval rho [(128,1)] at pa
    simp only [eval,Int.cast_one,one_mul,add_zero] at pa
    change eval rho [(23036,1)]=eval rho [(0,1),(127,-1)]
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul,zero]
    simpa only [eval,Int.cast_one,one_mul,add_zero,sub_eq_add_neg] using pa.trans h.2.1
  · change some (true,.linear [] [(23038,1)])=some hint at found
    cases found
    have h:=primitive 6 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(42,1)]) (rho 127) (rho 128) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    have pb:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 19 (by decide)
    change rho 23038=eval rho [(42,1)]*eval rho [(127,1)] at pb
    simp only [eval,Int.cast_one,one_mul,add_zero] at pb
    change eval rho []=eval rho [(23038,1)]
    simpa only [eval,Int.cast_one,one_mul,add_zero] using (pb.trans h.2.2).symm
  · change some (true,.square [(129,1)] [(129,1)])=some hint at found
    cases found
    have h:=primitive 7 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(0,-1),(43,1)]) (rho 129) (rho 130) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    change Square (eval rho [(129,1)]) (eval rho [(129,1)])
    simpa only [eval,Int.cast_one,one_mul,add_zero] using h.1
  · change some (true,.linear [(23040,1)] [(0,1),(129,-1)])=some hint at found
    cases found
    have h:=primitive 7 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(0,-1),(43,1)]) (rho 129) (rho 130) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    have pa:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 20 (by decide)
    change rho 23040=eval rho [(0,-1),(43,1)]*eval rho [(130,1)] at pa
    simp only [eval,Int.cast_one,one_mul,add_zero] at pa
    change eval rho [(23040,1)]=eval rho [(0,1),(129,-1)]
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul,zero]
    simpa only [eval,Int.cast_one,one_mul,add_zero,sub_eq_add_neg] using pa.trans h.2.1
  · change some (true,.linear [] [(23042,1)])=some hint at found
    cases found
    have h:=primitive 7 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(0,-1),(43,1)]) (rho 129) (rho 130) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    have pb:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 21 (by decide)
    change rho 23042=eval rho [(0,-1),(43,1)]*eval rho [(129,1)] at pb
    simp only [eval,Int.cast_one,one_mul,add_zero] at pb
    change eval rho []=eval rho [(23042,1)]
    simpa only [eval,Int.cast_one,one_mul,add_zero] using (pb.trans h.2.2).symm
  · change some (true,.linear [] [(23046,1)])=some hint at found
    cases found
    have b:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 22 (by decide)
    have c:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 23 (by decide)
    change rho 23044=eval rho [(127,1)]*eval rho [(129,1)] at b
    change rho 23046=eval rho [(10,1)]*eval rho [(23044,1)] at c
    simp only [eval,Int.cast_one,one_mul,add_zero] at b c
    change eval rho []=eval rho [(23046,1)]
    have g:=guards 3 (by decide)
    change rho 10*(rho 127*rho 129)=0 at g
    simpa only [eval,Int.cast_one,one_mul,add_zero] using (c.trans ((congrArg (fun value => rho 10*value) b).trans g)).symm
  · change some (true,.square [(131,1)] [(131,1)])=some hint at found
    cases found
    have h:=primitive 8 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(0,2613035198500699080012737903016384954916552590968062488514021062113153911183),(42,1)]) (rho 131) (rho 132) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    change Square (eval rho [(131,1)]) (eval rho [(131,1)])
    simpa only [eval,Int.cast_one,one_mul,add_zero] using h.1
  · change some (true,.linear [(23048,1)] [(0,1),(131,-1)])=some hint at found
    cases found
    have h:=primitive 8 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(0,2613035198500699080012737903016384954916552590968062488514021062113153911183),(42,1)]) (rho 131) (rho 132) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    have pa:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 24 (by decide)
    change rho 23048=eval rho [(0,2613035198500699080012737903016384954916552590968062488514021062113153911183),(42,1)]*eval rho [(132,1)] at pa
    simp only [eval,Int.cast_one,one_mul,add_zero] at pa
    change eval rho [(23048,1)]=eval rho [(0,1),(131,-1)]
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul,zero]
    simpa only [eval,Int.cast_one,one_mul,add_zero,sub_eq_add_neg] using pa.trans h.2.1
  · change some (true,.linear [] [(23050,1)])=some hint at found
    cases found
    have h:=primitive 8 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(0,2613035198500699080012737903016384954916552590968062488514021062113153911183),(42,1)]) (rho 131) (rho 132) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    have pb:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 25 (by decide)
    change rho 23050=eval rho [(0,2613035198500699080012737903016384954916552590968062488514021062113153911183),(42,1)]*eval rho [(131,1)] at pb
    simp only [eval,Int.cast_one,one_mul,add_zero] at pb
    change eval rho []=eval rho [(23050,1)]
    simpa only [eval,Int.cast_one,one_mul,add_zero] using (pb.trans h.2.2).symm
  · change some (true,.square [(133,1)] [(133,1)])=some hint at found
    cases found
    have h:=primitive 9 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(0,23326889571876200994796012627856472314977644248009733575144307806885254871463),(43,1)]) (rho 133) (rho 134) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    change Square (eval rho [(133,1)]) (eval rho [(133,1)])
    simpa only [eval,Int.cast_one,one_mul,add_zero] using h.1
  · change some (true,.linear [(23052,1)] [(0,1),(133,-1)])=some hint at found
    cases found
    have h:=primitive 9 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(0,23326889571876200994796012627856472314977644248009733575144307806885254871463),(43,1)]) (rho 133) (rho 134) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    have pa:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 26 (by decide)
    change rho 23052=eval rho [(0,23326889571876200994796012627856472314977644248009733575144307806885254871463),(43,1)]*eval rho [(134,1)] at pa
    simp only [eval,Int.cast_one,one_mul,add_zero] at pa
    change eval rho [(23052,1)]=eval rho [(0,1),(133,-1)]
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul,zero]
    simpa only [eval,Int.cast_one,one_mul,add_zero,sub_eq_add_neg] using pa.trans h.2.1
  · change some (true,.linear [] [(23054,1)])=some hint at found
    cases found
    have h:=primitive 9 (by decide)
    change CompilerZeroTest65.Primitive (eval rho [(0,23326889571876200994796012627856472314977644248009733575144307806885254871463),(43,1)]) (rho 133) (rho 134) at h
    simp only [CompilerZeroTest65.Primitive,eval,Int.cast_one,one_mul,add_zero] at h
    have pb:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 27 (by decide)
    change rho 23054=eval rho [(0,23326889571876200994796012627856472314977644248009733575144307806885254871463),(43,1)]*eval rho [(133,1)] at pb
    simp only [eval,Int.cast_one,one_mul,add_zero] at pb
    change eval rho []=eval rho [(23054,1)]
    simpa only [eval,Int.cast_one,one_mul,add_zero] using (pb.trans h.2.2).symm
  · change some (true,.linear [] [(23058,1)])=some hint at found
    cases found
    have b:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 28 (by decide)
    have c:=CapturedRegisteredAudit70.product_value rho linked arithmeticSat 29 (by decide)
    change rho 23056=eval rho [(131,1)]*eval rho [(133,1)] at b
    change rho 23058=eval rho [(10,1)]*eval rho [(23056,1)] at c
    simp only [eval,Int.cast_one,one_mul,add_zero] at b c
    change eval rho []=eval rho [(23058,1)]
    have g:=guards 4 (by decide)
    change rho 10*(rho 131*rho 133)=0 at g
    simpa only [eval,Int.cast_one,one_mul,add_zero] using (c.trans ((congrArg (fun value => rho 10*value) b).trans g)).symm
theorem registered_iff (rho : Nat → F) (zero : rho 0=1) (linked : rho copy=rho 0)
    (arithmeticSat : Satisfies rho CapturedRegisteredAudit70.arithmetic) :
    SatisfiesAt rho CapturedRegisteredAudit70.block.actual 35 ↔
    CapturedRegisteredAudit70.Primitive rho ∧ CapturedRegisteredAudit71.Guards rho := by
  constructor
  · intro sat
    exact ⟨CapturedRegisteredAudit71.actual_primitive rho zero linked arithmeticSat sat,
      CapturedRegisteredAudit71.actual_guards rho linked arithmeticSat sat⟩
  · rintro ⟨primitive,guards⟩
    exact primitive_assertions rho zero linked arithmeticSat primitive guards
end ShielddSecurity.CapturedRegisteredAssertions73

set_option pp.all true in
#check @ShielddSecurity.CapturedRegisteredAssertions73.primitive_assertions
#print axioms ShielddSecurity.CapturedRegisteredAssertions73.primitive_assertions
set_option pp.all true in
#check @ShielddSecurity.CapturedRegisteredAssertions73.registered_iff
#print axioms ShielddSecurity.CapturedRegisteredAssertions73.registered_iff
