import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0031
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(7936,8063),(7937,8064),(7938,8065),(7939,8066),(7940,8067),(7941,8068),(7942,8069),(7943,8070),(7944,8071),(7945,8072),(7946,8073),(7947,8074),(7948,8075),(7949,8076),(7950,8077),(7951,8078),(7952,8079),(7953,8080),(7954,8081),(7955,8082),(7956,8083),(7957,8084),(7958,8085),(7959,8086),(7960,8087),(7961,8088),(7962,8089),(7963,8090),(7964,8091),(7965,8092),(7966,8093),(7967,8094),(7968,8095),(7969,8096),(7970,8097),(7971,8098),(7972,8099),(7973,8100),(7974,8101),(7975,8102),(7976,8103),(7977,8104),(7978,8105),(7979,8106),(7980,8107),(7981,8108),(7982,8109),(7983,8110),(7984,8111),(7985,8112),(7986,8113),(7987,8114),(7988,8115),(7989,8116),(7990,8117),(7991,8118),(7992,8119),(7993,8120),(7994,8121),(7995,8122),(7996,8123),(7997,8124),(7998,8125),(7999,8126),(8001,8127),(8002,8128),(8003,8129),(8004,8130),(8005,8131),(8006,8132),(8007,8133),(8008,8134),(8009,8135),(8010,8136),(8011,8137),(8012,8138),(8013,8139),(8014,8140),(8015,8141),(8016,8142),(8017,8143),(8018,8144),(8019,8145),(8020,8146),(8021,8147),(8022,8148),(8023,8149),(8024,8150),(8025,8151),(8026,8152),(8027,8153),(8028,8154),(8029,8155),(8030,8156),(8031,8157),(8032,8158),(8033,8159),(8034,8160),(8035,8161),(8036,8162),(8037,8163),(8038,8164),(8039,8165),(8040,8166),(8041,8167),(8042,8168),(8043,8169),(8044,8170),(8045,8171),(8046,8172),(8047,8173),(8048,8174),(8049,8175),(8050,8176),(8051,8177),(8052,8178),(8053,8179),(8054,8180),(8055,8181),(8056,8182),(8057,8183),(8058,8184),(8059,8185),(8060,8186),(8061,8187),(8062,8188),(8063,8189),(8064,8190),(8065,8191),(8066,8192),(8067,8193),(8068,8194),(8069,8195),(8070,8196),(8071,8197),(8072,8198),(8073,8199),(8074,8200),(8075,8201),(8076,8202),(8077,8203),(8078,8204),(8079,8205),(8080,8206),(8081,8207),(8082,8208),(8083,8209),(8084,8210),(8085,8211),(8086,8212),(8087,8213),(8088,8214),(8089,8215),(8090,8216),(8091,8217),(8092,8218),(8093,8219),(8094,8220),(8095,8221),(8096,8222),(8097,8223),(8098,8224),(8099,8225),(8100,8226),(8101,8227),(8102,8228),(8103,8229),(8104,8230),(8105,8231),(8106,8232),(8107,8233),(8108,8234),(8109,8235),(8110,8236),(8111,8237),(8112,8238),(8113,8239),(8114,8240),(8115,8241),(8116,8242),(8117,8243),(8118,8244),(8119,8245),(8120,8246),(8121,8247),(8122,8248),(8123,8249),(8124,8250),(8125,8251),(8126,8252),(8127,8253),(8128,8254),(8131,8255),(8132,8257),(8133,8258),(8134,8259),(8135,8260),(8136,8261),(8137,8262),(8138,8263),(8139,8264),(8140,8265),(8141,8266),(8142,8267),(8143,8268),(8144,8269),(8145,8270),(8146,8271),(8147,8272),(8148,8273),(8149,8274),(8150,8275),(8151,8276),(8152,8277),(8153,8278),(8154,8279),(8155,8280),(8156,8281),(8157,8282),(8158,8283),(8159,8284),(8160,8285),(8161,8286),(8162,8287),(8163,8288),(8164,8289),(8165,8290),(8166,8291),(8167,8292),(8168,8293),(8169,8294),(8170,8295),(8171,8296),(8172,8297),(8173,8298),(8174,8299),(8175,8300),(8176,8301),(8177,8302),(8178,8303),(8179,8304),(8180,8305),(8181,8306),(8182,8307),(8183,8308),(8184,8309),(8185,8310),(8186,8311),(8187,8312),(8188,8313),(8189,8314),(8190,8315),(8191,8316)]
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
end ShielddSecurity.CapturedBooleanSlots208B0031

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0031.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0031.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0031.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0031.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0031.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0031.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0031.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0031.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0031.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0031.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0031.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0031.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0031.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0031.sound
