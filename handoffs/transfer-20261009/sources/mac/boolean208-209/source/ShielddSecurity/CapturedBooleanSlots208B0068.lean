import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0068
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(17408,17596),(17409,17597),(17410,17598),(17411,17599),(17412,17600),(17413,17601),(17414,17602),(17415,17603),(17416,17604),(17417,17605),(17418,17606),(17419,17607),(17420,17608),(17421,17609),(17422,17610),(17423,17611),(17424,17612),(17425,17613),(17426,17614),(17427,17615),(17428,17616),(17429,17617),(17430,17618),(17431,17619),(17432,17620),(17433,17621),(17434,17622),(17435,17623),(17436,17624),(17437,17625),(17438,17626),(17439,17627),(17440,17628),(17441,17629),(17442,17630),(17443,17631),(17444,17632),(17445,17633),(17446,17634),(17447,17635),(17448,17636),(17449,17637),(17450,17638),(17451,17639),(17452,17640),(17453,17641),(17454,17642),(17455,17643),(17456,17644),(17457,17645),(17458,17646),(17459,17647),(17460,17648),(17461,17649),(17462,17650),(17463,17651),(17464,17652),(17465,17653),(17466,17654),(17467,17655),(17468,17656),(17469,17657),(17470,17658),(17471,17659),(17472,17660),(17473,17661),(17474,17662),(17475,17663),(17476,17664),(17477,17665),(17478,17666),(17479,17667),(17480,17668),(17481,17669),(17485,17670),(17486,17671),(17487,17672),(17488,17673),(17489,17674),(17490,17675),(17491,17676),(17492,17677),(17493,17678),(17494,17679),(17495,17680),(17496,17681),(17497,17682),(17498,17683),(17499,17684),(17500,17685),(17501,17686),(17502,17687),(17503,17688),(17504,17689),(17505,17690),(17506,17691),(17507,17692),(17508,17693),(17509,17694),(17510,17695),(17511,17696),(17512,17697),(17513,17698),(17514,17699),(17515,17700),(17516,17701),(17517,17702),(17518,17703),(17519,17704),(17520,17705),(17521,17706),(17522,17707),(17523,17708),(17524,17709),(17525,17710),(17526,17711),(17527,17712),(17528,17713),(17529,17714),(17530,17715),(17531,17716),(17532,17717),(17533,17718),(17534,17719),(17535,17720),(17536,17721),(17537,17722),(17538,17723),(17539,17724),(17540,17725),(17541,17726),(17542,17727),(17543,17728),(17544,17729),(17545,17730),(17546,17731),(17547,17732),(17548,17733),(17549,17734),(17550,17735),(17551,17736),(17552,17737),(17553,17738),(17554,17739),(17555,17740),(17556,17741),(17557,17742),(17558,17743),(17559,17744),(17560,17745),(17561,17746),(17562,17747),(17563,17748),(17564,17749),(17565,17750),(17566,17751),(17567,17752),(17568,17753),(17569,17754),(17570,17755),(17571,17756),(17572,17757),(17573,17758),(17574,17759),(17575,17760),(17576,17761),(17577,17762),(17578,17763),(17579,17764),(17580,17765),(17581,17766),(17582,17767),(17583,17768),(17584,17769),(17585,17770),(17586,17771),(17587,17772),(17588,17773),(17589,17774),(17590,17775),(17591,17776),(17592,17777),(17593,17778),(17594,17779),(17595,17780),(17596,17781),(17597,17782),(17598,17783),(17599,17784),(17600,17785),(17601,17786),(17602,17787),(17603,17788),(17604,17789),(17605,17790),(17606,17791),(17607,17792),(17608,17793),(17609,17794),(17610,17795),(17611,17796),(17612,17797),(17613,17798),(17614,17799),(17615,17800),(17616,17801),(17617,17802),(17618,17803),(17619,17804),(17620,17805),(17621,17806),(17622,17807),(17623,17808),(17624,17809),(17625,17810),(17626,17811),(17627,17812),(17628,17813),(17629,17814),(17630,17815),(17631,17816),(17632,17817),(17633,17818),(17634,17819),(17635,17820),(17636,17821),(17637,17822),(17638,17823),(17639,17824),(17640,17825),(17641,17826),(17642,17827),(17643,17828),(17644,17829),(17645,17830),(17646,17831),(17647,17832),(17648,17833),(17649,17834),(17650,17835),(17651,17836),(17652,17837),(17653,17838),(17654,17839),(17655,17840),(17656,17841),(17657,17842),(17658,17843),(17659,17844),(17660,17845),(17661,17846),(17662,17847),(17663,17848)]
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
end ShielddSecurity.CapturedBooleanSlots208B0068

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0068.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0068.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0068.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0068.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0068.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0068.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0068.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0068.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0068.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0068.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0068.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0068.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0068.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0068.sound
