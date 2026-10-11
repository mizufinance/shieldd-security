import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0069
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(17664,17849),(17665,17850),(17666,17851),(17667,17852),(17668,17853),(17669,17854),(17670,17855),(17671,17856),(17672,17857),(17673,17858),(17674,17859),(17675,17860),(17676,17861),(17677,17862),(17678,17863),(17679,17864),(17680,17865),(17681,17866),(17682,17867),(17683,17868),(17684,17869),(17685,17870),(17686,17871),(17687,17872),(17688,17873),(17689,17874),(17690,17875),(17691,17876),(17692,17877),(17693,17878),(17694,17879),(17695,17880),(17696,17881),(17697,17882),(17698,17883),(17699,17884),(17700,17885),(17701,17886),(17702,17887),(17703,17888),(17704,17889),(17705,17890),(17706,17891),(17707,17892),(17708,17893),(17709,17894),(17710,17895),(17711,17896),(17712,17897),(17713,17898),(17714,17899),(17715,17900),(17716,17901),(17717,17902),(17718,17903),(17719,17904),(17720,17905),(17721,17906),(17722,17907),(17723,17908),(17724,17909),(17725,17910),(17726,17911),(17727,17912),(17728,17913),(17729,17914),(17730,17915),(17731,17916),(17732,17917),(17733,17918),(17734,17919),(17735,17920),(17736,17921),(17737,17922),(17738,17923),(17739,17924),(17743,17925),(17744,17926),(17745,17927),(17746,17928),(17747,17929),(17748,17930),(17749,17931),(17750,17932),(17751,17933),(17752,17934),(17753,17935),(17754,17936),(17755,17937),(17756,17938),(17757,17939),(17758,17940),(17759,17941),(17760,17942),(17761,17943),(17762,17944),(17763,17945),(17764,17946),(17765,17947),(17766,17948),(17767,17949),(17768,17950),(17769,17951),(17770,17952),(17771,17953),(17772,17954),(17773,17955),(17774,17956),(17775,17957),(17776,17958),(17777,17959),(17778,17960),(17779,17961),(17780,17962),(17781,17963),(17782,17964),(17783,17965),(17784,17966),(17785,17967),(17786,17968),(17787,17969),(17788,17970),(17789,17971),(17790,17972),(17791,17973),(17792,17974),(17793,17975),(17794,17976),(17795,17977),(17796,17978),(17797,17979),(17798,17980),(17799,17981),(17800,17982),(17801,17983),(17802,17984),(17803,17985),(17804,17986),(17805,17987),(17806,17988),(17807,17989),(17808,17990),(17809,17991),(17810,17992),(17811,17993),(17812,17994),(17813,17995),(17814,17996),(17815,17997),(17816,17998),(17817,17999),(17818,18000),(17819,18001),(17820,18002),(17821,18003),(17822,18004),(17823,18005),(17824,18006),(17825,18007),(17826,18008),(17827,18009),(17828,18010),(17829,18011),(17830,18012),(17831,18013),(17832,18014),(17833,18015),(17834,18016),(17835,18017),(17836,18018),(17837,18019),(17838,18020),(17839,18021),(17840,18022),(17841,18023),(17842,18024),(17843,18025),(17844,18026),(17845,18027),(17846,18028),(17847,18029),(17848,18030),(17849,18031),(17850,18032),(17851,18033),(17852,18034),(17853,18035),(17854,18036),(17855,18037),(17856,18038),(17857,18039),(17858,18040),(17859,18041),(17860,18042),(17861,18043),(17862,18044),(17863,18045),(17864,18046),(17865,18047),(17866,18048),(17867,18049),(17868,18050),(17869,18051),(17870,18052),(17871,18053),(17872,18054),(17873,18055),(17874,18056),(17875,18057),(17876,18058),(17877,18059),(17878,18060),(17879,18061),(17880,18062),(17881,18063),(17882,18064),(17883,18065),(17884,18066),(17885,18067),(17886,18068),(17887,18069),(17888,18070),(17889,18071),(17890,18072),(17891,18073),(17892,18074),(17893,18075),(17894,18076),(17895,18077),(17896,18078),(17897,18079),(17898,18080),(17899,18081),(17900,18082),(17901,18083),(17902,18084),(17903,18085),(17904,18086),(17905,18087),(17906,18088),(17907,18089),(17908,18090),(17909,18091),(17910,18092),(17911,18093),(17912,18094),(17913,18095),(17914,18096),(17915,18097),(17916,18098),(17917,18099),(17918,18100),(17919,18101)]
theorem count : slots.length=253 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0069

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0069.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0069.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0069.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0069.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0069.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0069.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0069.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0069.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0069.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0069.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0069.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0069.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0069.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0069.sound
