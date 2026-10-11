import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0003
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(768,813),(769,814),(770,815),(771,816),(772,817),(773,818),(774,819),(775,820),(776,821),(777,822),(778,823),(779,824),(780,825),(781,826),(782,827),(783,828),(784,829),(785,830),(786,831),(787,832),(788,833),(789,834),(790,835),(791,836),(792,837),(793,838),(794,839),(795,840),(796,841),(797,842),(798,843),(799,844),(800,845),(801,846),(802,847),(803,848),(804,849),(805,850),(806,851),(807,852),(808,853),(809,854),(810,855),(811,856),(812,857),(813,858),(814,859),(815,860),(816,861),(817,862),(818,863),(819,864),(820,865),(821,866),(822,867),(823,868),(824,869),(825,870),(826,871),(827,872),(828,873),(829,874),(830,875),(831,876),(832,877),(833,878),(834,879),(835,880),(836,881),(837,882),(838,883),(839,884),(840,885),(841,886),(842,887),(843,888),(844,889),(845,890),(846,891),(847,892),(848,893),(849,894),(850,895),(851,896),(852,897),(853,898),(854,899),(855,900),(856,901),(857,902),(858,903),(859,904),(860,905),(861,906),(862,907),(863,908),(864,909),(865,910),(866,911),(867,912),(868,913),(869,914),(870,915),(871,916),(872,917),(873,918),(874,919),(875,920),(876,921),(877,922),(878,923),(879,924),(880,925),(881,926),(882,927),(883,928),(884,929),(885,930),(886,931),(887,932),(888,933),(889,934),(890,935),(891,936),(892,937),(893,938),(894,939),(895,940),(896,941),(897,942),(898,943),(899,944),(900,945),(901,946),(902,947),(903,948),(904,949),(905,950),(906,951),(907,952),(908,953),(909,954),(910,955),(911,956),(912,957),(913,958),(914,959),(915,960),(916,961),(917,962),(918,963),(919,964),(920,965),(921,966),(922,967),(923,968),(924,969),(925,970),(926,971),(927,972),(928,973),(929,974),(930,975),(931,976),(932,977),(933,978),(934,979),(935,980),(939,981),(940,983),(941,984),(942,985),(943,986),(944,987),(945,988),(946,989),(947,990),(948,991),(949,992),(950,993),(951,994),(952,995),(953,996),(954,997),(955,998),(956,999),(957,1000),(958,1001),(959,1002),(960,1003),(961,1004),(962,1005),(963,1006),(964,1007),(965,1008),(966,1009),(967,1010),(968,1011),(969,1012),(970,1013),(971,1014),(972,1015),(973,1016),(974,1017),(975,1018),(976,1019),(977,1020),(978,1021),(979,1022),(980,1023),(981,1024),(982,1025),(983,1026),(984,1027),(985,1028),(986,1029),(987,1030),(988,1031),(989,1032),(990,1033),(991,1034),(992,1035),(993,1036),(994,1037),(995,1038),(996,1039),(997,1040),(998,1041),(999,1042),(1000,1043),(1001,1044),(1002,1045),(1003,1046),(1004,1047),(1005,1048),(1006,1049),(1007,1050),(1008,1051),(1009,1052),(1010,1053),(1011,1054),(1012,1055),(1013,1056),(1014,1057),(1015,1058),(1016,1059),(1017,1060),(1018,1061),(1019,1062),(1020,1063),(1021,1064),(1022,1065),(1023,1066)]
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
end ShielddSecurity.CapturedBooleanSlots208B0003

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0003.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0003.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0003.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0003.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0003.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0003.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0003.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0003.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0003.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0003.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0003.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0003.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0003.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0003.sound
