import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0081
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(20736,20710),(20737,20711),(20738,20712),(20739,20713),(20740,20714),(20741,20715),(20742,20716),(20743,20717),(20744,20718),(20745,20719),(20746,20720),(20747,20721),(20748,20722),(20749,20723),(20750,20724),(20751,20725),(20752,20726),(20753,20727),(20754,20728),(20755,20729),(20756,20730),(20757,20731),(20758,20732),(20759,20733),(20760,20734),(20761,20735),(20762,20736),(20763,20737),(20764,20738),(20765,20739),(20766,20740),(20767,20741),(20768,20742),(20769,20743),(20770,20744),(20771,20745),(20772,20746),(20773,20747),(20774,20748),(20775,20749),(20776,20750),(20777,20751),(20778,20752),(20779,20753),(20780,20754),(20781,20755),(20782,20756),(20783,20757),(20784,20758),(20785,20759),(20786,20760),(20787,20761),(20788,20762),(20789,20763),(20790,20764),(20791,20765),(20792,20766),(20793,20767),(20794,20768),(20795,20769),(20796,20770),(20797,20771),(20798,20772),(20799,20773),(20800,20774),(20801,20775),(20802,20776),(20803,20777),(20804,20778),(20805,20779),(20806,20780),(20807,20781),(20808,20782),(20809,20783),(20810,20784),(20811,20785),(20812,20786),(20813,20787),(20814,20788),(20815,20789),(20816,20790),(20817,20791),(20818,20792),(20819,20793),(20820,20794),(20821,20795),(20822,20796),(20823,20797),(20824,20798),(20825,20799),(20826,20800),(20827,20801),(20828,20802),(20829,20803),(20830,20804),(20831,20805),(20832,20806),(20833,20807),(20834,20808),(20835,20809),(20836,20810),(20837,20811),(20838,20812),(20839,20813),(20840,20814),(20841,20815),(20842,20816),(20843,20817),(20844,20818),(20845,20819),(20846,20820),(20847,20821),(20848,20822),(20849,20823),(20850,20824),(20851,20825),(20852,20826),(20853,20827),(20854,20828),(20855,20829),(20856,20830),(20857,20831),(20858,20832),(20859,20833),(20860,20834),(20861,20835),(20862,20836),(20863,20837),(20864,20838),(20865,20839),(20866,20840),(20867,20841),(20868,20842),(20869,20843),(20870,20844),(20871,20845),(20872,20846),(20873,20847),(20874,20848),(20875,20849),(20876,20850),(20877,20851),(20878,20852),(20879,20853),(20880,20854),(20881,20855),(20882,20856),(20883,20857),(20884,20858),(20885,20859),(20886,20860),(20887,20861),(20888,20862),(20889,20863),(20890,20864),(20891,20865),(20892,20866),(20893,20867),(20894,20868),(20895,20869),(20896,20870),(20897,20871),(20898,20872),(20899,20873),(20900,20874),(20901,20875),(20902,20876),(20903,20877),(20904,20878),(20905,20879),(20906,20880),(20907,20881),(20908,20882),(20909,20883),(20910,20884),(20911,20885),(20912,20886),(20913,20887),(20914,20888),(20915,20889),(20916,20890),(20917,20891),(20918,20892),(20919,20893),(20920,20894),(20921,20895),(20922,20896),(20923,20897),(20924,20898),(20925,20899),(20926,20900),(20927,20901),(20928,20902),(20929,20903),(20930,20904),(20931,20905),(20932,20906),(20933,20907),(20934,20908),(20935,20909),(20936,20910),(20937,20911),(20938,20912),(20939,20913),(20940,20914),(20941,20915),(20942,20916),(20943,20917),(20944,20918),(20945,20919),(20946,20920),(20947,20921),(20948,20922),(20949,20923),(20950,20924),(20951,20925),(20952,20926),(20953,20927),(20954,20928),(20955,20929),(20956,20930),(20957,20931),(20958,20932),(20959,20933)]
theorem count : slots.length=224 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0081

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0081.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0081.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0081.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0081.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0081.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0081.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0081.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0081.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0081.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0081.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0081.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0081.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0081.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0081.sound
