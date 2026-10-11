import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0032
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(8192,8317),(8193,8318),(8194,8319),(8195,8320),(8196,8321),(8197,8322),(8198,8323),(8199,8324),(8200,8325),(8201,8326),(8202,8327),(8203,8328),(8204,8329),(8205,8330),(8206,8331),(8207,8332),(8208,8333),(8209,8334),(8210,8335),(8211,8336),(8212,8337),(8213,8338),(8214,8339),(8215,8340),(8216,8341),(8217,8342),(8218,8343),(8219,8344),(8220,8345),(8221,8346),(8222,8347),(8223,8348),(8224,8349),(8225,8350),(8226,8351),(8227,8352),(8228,8353),(8229,8354),(8230,8355),(8231,8356),(8232,8357),(8233,8358),(8234,8359),(8235,8360),(8236,8361),(8237,8362),(8238,8363),(8239,8364),(8240,8365),(8241,8366),(8242,8367),(8243,8368),(8244,8369),(8245,8370),(8246,8371),(8247,8372),(8248,8373),(8249,8374),(8250,8375),(8251,8376),(8252,8377),(8253,8378),(8254,8379),(8255,8380),(8256,8381),(8257,8382),(8258,8383),(8259,8384),(8265,8460),(8266,8461),(8267,8462),(8268,8463),(8269,8464),(8270,8465),(8271,8466),(8272,8467),(8273,8468),(8274,8469),(8275,8470),(8276,8471),(8277,8472),(8278,8473),(8279,8474),(8280,8475),(8281,8476),(8282,8477),(8283,8478),(8284,8479),(8285,8480),(8286,8481),(8287,8482),(8288,8483),(8289,8484),(8290,8485),(8291,8486),(8292,8487),(8293,8488),(8294,8489),(8295,8490),(8296,8491),(8297,8492),(8298,8493),(8299,8494),(8300,8495),(8301,8496),(8302,8497),(8303,8498),(8304,8499),(8305,8500),(8306,8501),(8307,8502),(8308,8503),(8309,8504),(8310,8505),(8311,8506),(8312,8507),(8319,8552),(8320,8553),(8321,8554),(8322,8555),(8323,8556),(8324,8557),(8325,8558),(8326,8559),(8327,8560),(8328,8561),(8329,8562),(8330,8563),(8331,8564),(8332,8565),(8333,8566),(8334,8567),(8335,8568),(8336,8569),(8337,8570),(8338,8571),(8339,8572),(8340,8573),(8341,8574),(8342,8575),(8343,8576),(8344,8577),(8345,8578),(8346,8579),(8347,8580),(8348,8581),(8349,8582),(8350,8583),(8351,8584),(8352,8585),(8353,8586),(8354,8587),(8355,8588),(8356,8589),(8357,8590),(8358,8591),(8359,8592),(8360,8593),(8361,8594),(8362,8595),(8363,8596),(8364,8597),(8365,8598),(8366,8599),(8367,8600),(8368,8601),(8369,8602),(8370,8603),(8371,8604),(8372,8605),(8373,8606),(8374,8607),(8375,8608),(8376,8609),(8377,8610),(8378,8611),(8379,8612),(8380,8613),(8381,8614),(8382,8615),(8383,8616),(8384,8617),(8385,8618),(8386,8619),(8387,8620),(8388,8621),(8389,8622),(8390,8623),(8391,8624),(8392,8625),(8393,8626),(8394,8627),(8395,8628),(8396,8629),(8397,8630),(8398,8631),(8399,8632),(8400,8633),(8401,8634),(8402,8635),(8403,8636),(8404,8637),(8405,8638),(8406,8639),(8407,8640),(8408,8641),(8409,8642),(8410,8643),(8411,8644),(8412,8645),(8413,8646),(8414,8647),(8415,8648),(8416,8649),(8417,8650),(8418,8651),(8419,8652),(8420,8653),(8421,8654),(8422,8655),(8423,8656),(8424,8657),(8425,8658),(8426,8659),(8427,8660),(8428,8661),(8429,8662),(8430,8663),(8431,8664),(8432,8665),(8433,8666),(8434,8667),(8435,8668),(8436,8669),(8437,8670),(8438,8671),(8439,8672),(8440,8673),(8441,8674),(8442,8675),(8443,8676),(8444,8677),(8445,8678),(8446,8679),(8447,8680)]
theorem count : slots.length=245 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0032

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0032.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0032.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0032.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0032.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0032.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0032.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0032.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0032.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0032.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0032.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0032.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0032.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0032.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0032.sound
