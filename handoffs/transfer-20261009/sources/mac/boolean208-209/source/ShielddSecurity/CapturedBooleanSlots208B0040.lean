import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0040
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(10371,10591),(10374,10594),(10375,10595),(10376,10596),(10377,10597),(10378,10598),(10379,10599),(10380,10600),(10381,10601),(10382,10602),(10383,10603),(10384,10604),(10385,10605),(10386,10606),(10387,10607),(10388,10608),(10389,10609),(10390,10610),(10391,10611),(10392,10612),(10393,10613),(10394,10614),(10395,10615),(10396,10616),(10397,10617),(10398,10618),(10399,10619),(10400,10620),(10401,10621),(10402,10622),(10403,10623),(10404,10624),(10405,10625),(10406,10626),(10407,10627),(10408,10628),(10409,10629),(10410,10630),(10411,10631),(10412,10632),(10413,10633),(10414,10634),(10415,10635),(10416,10636),(10417,10637),(10418,10638),(10419,10639),(10420,10640),(10421,10641),(10422,10642),(10423,10643),(10424,10644),(10425,10645),(10426,10646),(10427,10647),(10428,10648),(10429,10649),(10430,10650),(10431,10651),(10432,10652),(10433,10653),(10434,10654),(10435,10655),(10436,10656),(10437,10657),(10438,10658),(10439,10659),(10440,10660),(10441,10661),(10442,10662),(10443,10663),(10444,10664),(10445,10665),(10446,10666),(10447,10667),(10448,10668),(10449,10669),(10450,10670),(10451,10671),(10452,10672),(10453,10673),(10454,10674),(10455,10675),(10456,10676),(10457,10677),(10458,10678),(10459,10679),(10460,10680),(10461,10681),(10462,10682),(10463,10683),(10464,10684),(10465,10685),(10466,10686),(10467,10687),(10468,10688),(10469,10689),(10470,10690),(10471,10691),(10472,10692),(10473,10693),(10474,10694),(10475,10695),(10476,10696),(10477,10697),(10478,10698),(10479,10699),(10480,10700),(10481,10701),(10482,10702),(10483,10703),(10484,10704),(10485,10705),(10486,10706),(10487,10707),(10488,10708),(10489,10709),(10490,10710),(10491,10711),(10492,10712),(10493,10713),(10494,10714),(10495,10715)]
theorem count : slots.length=123 := rfl
theorem checked : checkSlots CapturedFullAssertions54.recipeAt slots=true := by decide
theorem originals : ∀ slot∈slots,3≤slot.2 ∧ slot.2<22738 := by decide
theorem positions : ∀ slot∈slots,slot.1<22816 := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (bits : Nat → Bool) (columns : List Nat)
 (coverage : ∀ slot∈slots,slot.2∈columns) : ∀ slot∈slots,
 ∃ row,CapturedFullRelation58.rowAt (177954+slot.1)=some row ∧
 Square (eval (CapturedFullRelation58.candidate (seeded base bits columns)) row.a)
        (eval (CapturedFullRelation58.candidate (seeded base bits columns)) row.b) :=
 fun slot member => candidate_selected base bits columns slots checked originals coverage positions slot member
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∀ slot∈slots,rho slot.2=0 ∨ rho slot.2=1 := by
 intro slot member
 obtain ⟨outlined,matching⟩:=checked_slot _ slots checked slot member
 have truth:=((CapturedFullRelation58.satisfies_iff rho).mp satisfied).2 slot.1
   (positions slot member) (outlined,wireRecipe slot.2) matching
 exact (wire_truth rho slot.2).mp truth
end ShielddSecurity.CapturedBooleanSlots208B0040

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0040.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0040.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0040.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0040.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0040.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0040.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0040.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0040.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0040.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0040.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0040.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0040.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0040.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0040.sound
