import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0052
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(13421,13630),(13422,13631),(13423,13632),(13424,13633),(13425,13634),(13426,13635),(13427,13636),(13428,13637),(13429,13638),(13430,13639),(13431,13640),(13432,13641),(13433,13642),(13434,13643),(13435,13644),(13436,13645),(13437,13646),(13438,13647),(13439,13648),(13440,13649),(13441,13650),(13442,13651),(13443,13652),(13444,13653),(13445,13654),(13446,13655),(13447,13656),(13448,13657),(13449,13658),(13450,13659),(13451,13660),(13452,13661),(13453,13662),(13454,13663),(13455,13664),(13456,13665),(13457,13666),(13458,13667),(13459,13668),(13460,13669),(13461,13670),(13462,13671),(13463,13672),(13464,13673),(13465,13674),(13466,13675),(13467,13676),(13468,13677),(13469,13678),(13470,13679),(13471,13680),(13472,13681),(13473,13682),(13474,13683),(13475,13684),(13476,13685),(13477,13686),(13478,13687),(13479,13688),(13480,13689),(13481,13690),(13482,13691),(13483,13692),(13484,13693),(13485,13694),(13486,13695),(13487,13696),(13488,13697),(13489,13698),(13490,13699),(13491,13700),(13492,13701),(13493,13702),(13494,13703),(13495,13704),(13496,13705),(13497,13706),(13498,13707),(13499,13708),(13500,13709),(13501,13710),(13502,13711),(13503,13712),(13504,13713),(13505,13714),(13506,13715),(13507,13716),(13508,13717),(13509,13718),(13510,13719),(13511,13720),(13512,13721),(13513,13722),(13514,13723),(13515,13724),(13516,13725),(13517,13726),(13518,13727),(13519,13728),(13520,13729),(13521,13730),(13522,13731),(13523,13732),(13524,13733),(13525,13734),(13526,13735),(13527,13736),(13528,13737),(13529,13738),(13530,13739),(13531,13740),(13532,13741),(13533,13742),(13534,13743),(13535,13744),(13536,13745),(13537,13746),(13538,13747),(13539,13748),(13540,13749),(13541,13750),(13542,13751),(13543,13752),(13544,13753),(13545,13754),(13546,13755),(13547,13756),(13548,13757),(13549,13758),(13550,13759),(13551,13760),(13552,13761),(13553,13762),(13554,13763),(13555,13764),(13556,13765),(13557,13766),(13558,13767),(13559,13768),(13560,13769),(13561,13770),(13562,13771),(13563,13772),(13564,13773),(13565,13774),(13566,13775),(13567,13776)]
theorem count : slots.length=147 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0052

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0052.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0052.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0052.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0052.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0052.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0052.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0052.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0052.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0052.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0052.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0052.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0052.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0052.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0052.sound
