import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0041
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(10496,10716),(10497,10717),(10498,10718),(10499,10719),(10500,10720),(10501,10721),(10502,10722),(10503,10723),(10504,10724),(10505,10725),(10506,10726),(10507,10727),(10508,10728),(10509,10729),(10510,10730),(10511,10731),(10512,10732),(10513,10733),(10514,10734),(10515,10735),(10516,10736),(10517,10737),(10518,10738),(10519,10739),(10520,10740),(10521,10741),(10522,10742),(10523,10743),(10524,10744),(10525,10745),(10526,10746),(10527,10747),(10528,10748),(10529,10749),(10530,10750),(10531,10751),(10532,10752),(10533,10753),(10534,10754),(10535,10755),(10536,10756),(10537,10757),(10538,10758),(10539,10759),(10540,10760),(10541,10761),(10542,10762),(10543,10763),(10544,10764),(10545,10765),(10546,10766),(10547,10767),(10548,10768),(10549,10769),(10550,10770),(10551,10771),(10552,10772),(10553,10773),(10554,10774),(10555,10775),(10556,10776),(10557,10777),(10558,10778),(10559,10779),(10560,10780),(10561,10781),(10562,10782),(10563,10783),(10564,10784),(10565,10785),(10566,10786),(10567,10787),(10568,10788),(10569,10789),(10570,10790),(10571,10791),(10572,10792),(10573,10793),(10574,10794),(10575,10795),(10576,10796),(10577,10797),(10578,10798),(10579,10799),(10580,10800),(10581,10801),(10582,10802),(10583,10803),(10584,10804),(10585,10805),(10586,10806),(10587,10807),(10588,10808),(10589,10809),(10590,10810),(10591,10811),(10592,10812),(10593,10813),(10594,10814),(10595,10815),(10596,10816),(10597,10817),(10598,10818),(10599,10819),(10600,10820),(10601,10821),(10602,10822),(10603,10823),(10604,10824),(10605,10825),(10606,10826),(10607,10827),(10608,10828),(10609,10829),(10610,10830),(10611,10831),(10612,10832),(10613,10833),(10614,10834),(10615,10835),(10616,10836),(10617,10837),(10618,10838),(10619,10839),(10620,10840),(10621,10841),(10622,10842),(10623,10843),(10624,10844),(10625,10845),(10626,10846),(10627,10847),(10628,10848),(10633,10849)]
theorem count : slots.length=134 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0041

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0041.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0041.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0041.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0041.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0041.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0041.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0041.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0041.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0041.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0041.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0041.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0041.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0041.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0041.sound
