import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0074
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(18944,19111),(18945,19112),(18946,19113),(18947,19114),(18948,19115),(18949,19116),(18950,19117),(18951,19118),(18952,19119),(18953,19120),(18954,19121),(18955,19122),(18956,19123),(18957,19124),(18958,19125),(18959,19126),(18960,19127),(18961,19128),(18962,19129),(18963,19130),(18964,19131),(18965,19132),(18966,19133),(18967,19134),(18968,19135),(18969,19136),(18970,19137),(18971,19138),(18972,19139),(18973,19140),(18974,19141),(18975,19142),(18976,19143),(18977,19144),(18978,19145),(18979,19146),(18980,19147),(18981,19148),(18982,19149),(18983,19150),(18984,19151),(18985,19152),(18986,19153),(18987,19154),(18988,19155),(18989,19156),(18990,19157),(18991,19158),(18992,19159),(18993,19160),(18994,19161),(18995,19162),(18996,19163),(18997,19164),(18998,19165),(18999,19166),(19000,19167),(19001,19168),(19002,19169),(19003,19170),(19004,19171),(19005,19172),(19006,19173),(19007,19174),(19008,19175),(19009,19176),(19010,19177),(19011,19178),(19012,19179),(19013,19180),(19014,19181),(19015,19182),(19016,19183),(19017,19184),(19018,19185),(19019,19186),(19020,19187),(19021,19188),(19022,19189),(19023,19190),(19024,19191),(19025,19192),(19026,19193),(19027,19194),(19028,19195),(19029,19196),(19030,19197),(19031,19198),(19032,19199),(19036,19200),(19037,19201),(19038,19202),(19039,19203),(19040,19204),(19041,19205),(19042,19206),(19043,19207),(19044,19208),(19045,19209),(19046,19210),(19047,19211),(19048,19212),(19049,19213),(19050,19214),(19051,19215),(19052,19216),(19053,19217),(19054,19218),(19055,19219),(19056,19220),(19057,19221),(19058,19222),(19059,19223),(19060,19224),(19061,19225),(19062,19226),(19063,19227),(19064,19228),(19065,19229),(19066,19230),(19067,19231),(19068,19232),(19069,19233),(19070,19234),(19071,19235),(19072,19236),(19073,19237),(19074,19238),(19075,19239),(19076,19240),(19077,19241),(19078,19242),(19079,19243),(19080,19244),(19081,19245),(19082,19246),(19083,19247),(19084,19248),(19085,19249),(19086,19250),(19087,19251),(19088,19252),(19089,19253),(19090,19254),(19091,19255),(19092,19256),(19093,19257),(19094,19258),(19095,19259),(19096,19260),(19097,19261),(19098,19262),(19099,19263),(19100,19264),(19101,19265),(19102,19266),(19103,19267),(19104,19268),(19105,19269),(19106,19270),(19107,19271),(19108,19272),(19109,19273),(19110,19274),(19111,19275),(19112,19276),(19113,19277),(19114,19278),(19115,19279),(19116,19280),(19117,19281),(19118,19282),(19119,19283),(19120,19284),(19121,19285),(19122,19286),(19123,19287),(19124,19288),(19125,19289),(19126,19290),(19127,19291),(19128,19292),(19129,19293),(19130,19294),(19131,19295),(19132,19296),(19133,19297),(19134,19298),(19135,19299),(19136,19300),(19137,19301),(19138,19302),(19139,19303),(19140,19304),(19141,19305),(19142,19306),(19143,19307),(19144,19308),(19145,19309),(19146,19310),(19147,19311),(19148,19312),(19149,19313),(19150,19314),(19151,19315),(19152,19316),(19153,19317),(19154,19318),(19155,19319),(19156,19320),(19157,19321),(19158,19322),(19159,19323),(19160,19324),(19161,19325),(19162,19326),(19163,19327),(19164,19328),(19165,19329),(19166,19330),(19167,19331),(19168,19332),(19169,19333),(19170,19334),(19171,19335),(19172,19336),(19173,19337),(19174,19338),(19175,19339),(19176,19340),(19177,19341),(19178,19342),(19179,19343),(19180,19344),(19181,19345),(19182,19346),(19183,19347),(19184,19348),(19185,19349),(19186,19350),(19187,19351),(19188,19352),(19189,19353),(19190,19354),(19191,19355),(19192,19356),(19193,19357),(19194,19358),(19195,19359),(19196,19360),(19197,19361),(19198,19362),(19199,19363)]
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
end ShielddSecurity.CapturedBooleanSlots208B0074

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0074.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0074.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0074.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0074.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0074.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0074.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0074.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0074.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0074.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0074.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0074.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0074.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0074.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0074.sound
