import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0071
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(18176,18355),(18177,18356),(18178,18357),(18179,18358),(18180,18359),(18181,18360),(18182,18361),(18183,18362),(18184,18363),(18185,18364),(18186,18365),(18187,18366),(18188,18367),(18189,18368),(18190,18369),(18191,18370),(18192,18371),(18193,18372),(18194,18373),(18195,18374),(18196,18375),(18197,18376),(18198,18377),(18199,18378),(18200,18379),(18201,18380),(18202,18381),(18203,18382),(18204,18383),(18205,18384),(18206,18385),(18207,18386),(18208,18387),(18209,18388),(18210,18389),(18211,18390),(18212,18391),(18213,18392),(18214,18393),(18215,18394),(18216,18395),(18217,18396),(18218,18397),(18219,18398),(18220,18399),(18221,18400),(18222,18401),(18223,18402),(18224,18403),(18225,18404),(18226,18405),(18227,18406),(18228,18407),(18229,18408),(18230,18409),(18231,18410),(18232,18411),(18233,18412),(18234,18413),(18235,18414),(18236,18415),(18237,18416),(18238,18417),(18239,18418),(18240,18419),(18241,18420),(18242,18421),(18243,18422),(18244,18423),(18245,18424),(18246,18425),(18247,18426),(18248,18427),(18249,18428),(18250,18429),(18251,18430),(18252,18431),(18253,18432),(18254,18433),(18255,18434),(18262,18435),(18263,18436),(18264,18437),(18265,18438),(18266,18439),(18267,18440),(18268,18441),(18269,18442),(18270,18443),(18271,18444),(18272,18445),(18273,18446),(18274,18447),(18275,18448),(18276,18449),(18277,18450),(18278,18451),(18279,18452),(18280,18453),(18281,18454),(18282,18455),(18283,18456),(18284,18457),(18285,18458),(18286,18459),(18287,18460),(18288,18461),(18289,18462),(18290,18463),(18291,18464),(18292,18465),(18293,18466),(18294,18467),(18295,18468),(18296,18469),(18297,18470),(18298,18471),(18299,18472),(18300,18473),(18301,18474),(18302,18475),(18303,18476),(18304,18477),(18305,18478),(18306,18479),(18307,18480),(18308,18481),(18309,18482),(18310,18483),(18311,18484),(18312,18485),(18313,18486),(18314,18487),(18315,18488),(18316,18489),(18317,18490),(18318,18491),(18319,18492),(18320,18493),(18321,18494),(18322,18495),(18323,18496),(18324,18497),(18325,18498),(18326,18499),(18327,18500),(18328,18501),(18329,18502),(18330,18503),(18331,18504),(18332,18505),(18333,18506),(18334,18507),(18335,18508),(18336,18509),(18337,18510),(18338,18511),(18339,18512),(18340,18513),(18341,18514),(18342,18515),(18343,18516),(18344,18517),(18345,18518),(18346,18519),(18347,18520),(18348,18521),(18349,18522),(18350,18523),(18351,18524),(18352,18525),(18353,18526),(18354,18527),(18355,18528),(18356,18529),(18357,18530),(18358,18531),(18359,18532),(18360,18533),(18361,18534),(18362,18535),(18363,18536),(18364,18537),(18365,18538),(18366,18539),(18367,18540),(18368,18541),(18369,18542),(18370,18543),(18371,18544),(18372,18545),(18373,18546),(18374,18547),(18375,18548),(18376,18549),(18377,18550),(18378,18551),(18379,18552),(18380,18553),(18381,18554),(18382,18555),(18383,18556),(18384,18557),(18385,18558),(18386,18559),(18387,18560),(18388,18561),(18389,18562),(18390,18563),(18391,18564),(18392,18565),(18393,18566),(18394,18567),(18395,18568),(18396,18569),(18397,18570),(18398,18571),(18399,18572),(18400,18573),(18401,18574),(18402,18575),(18403,18576),(18404,18577),(18405,18578),(18406,18579),(18407,18580),(18408,18581),(18409,18582),(18410,18583),(18411,18584),(18412,18585),(18413,18586),(18414,18587),(18415,18588),(18416,18589),(18417,18590),(18418,18591),(18419,18592),(18420,18593),(18421,18594),(18422,18595),(18423,18596),(18424,18597),(18425,18598),(18426,18599),(18427,18600),(18428,18601),(18429,18602),(18430,18603),(18431,18604)]
theorem count : slots.length=250 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0071

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0071.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0071.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0071.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0071.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0071.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0071.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0071.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0071.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0071.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0071.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0071.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0071.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0071.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0071.sound
