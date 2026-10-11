import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0024
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(6144,6282),(6145,6283),(6146,6284),(6147,6285),(6148,6286),(6149,6287),(6150,6288),(6151,6289),(6152,6290),(6153,6291),(6154,6292),(6155,6293),(6156,6294),(6157,6295),(6158,6296),(6159,6297),(6160,6298),(6161,6299),(6162,6300),(6163,6301),(6164,6302),(6165,6303),(6166,6304),(6167,6305),(6168,6306),(6169,6307),(6170,6308),(6171,6309),(6172,6310),(6173,6311),(6174,6312),(6175,6313),(6176,6314),(6177,6315),(6178,6316),(6179,6317),(6180,6318),(6181,6319),(6182,6320),(6183,6321),(6184,6322),(6185,6323),(6188,6335),(6189,6336),(6190,6337),(6191,6338),(6192,6339),(6193,6340),(6194,6341),(6195,6342),(6196,6343),(6197,6344),(6198,6345),(6199,6346),(6200,6347),(6201,6348),(6202,6349),(6203,6350),(6204,6351),(6205,6352),(6206,6353),(6207,6354),(6208,6355),(6209,6356),(6210,6357),(6211,6358),(6212,6359),(6213,6360),(6214,6361),(6215,6362),(6216,6363),(6217,6364),(6218,6365),(6219,6366),(6220,6367),(6221,6368),(6222,6369),(6223,6370),(6224,6371),(6225,6372),(6226,6373),(6227,6374),(6228,6375),(6229,6376),(6230,6377),(6231,6378),(6232,6379),(6233,6380),(6234,6381),(6235,6382),(6236,6383),(6237,6384),(6238,6385),(6239,6386),(6240,6387),(6241,6388),(6242,6389),(6243,6390),(6244,6391),(6245,6392),(6246,6393),(6247,6394),(6248,6395),(6249,6396),(6250,6397),(6251,6398),(6252,6399),(6253,6400),(6254,6401),(6255,6402),(6256,6403),(6257,6404),(6258,6405),(6259,6406),(6260,6407),(6261,6408),(6262,6409),(6263,6410),(6264,6411),(6265,6412),(6266,6413),(6267,6414),(6268,6415),(6269,6416),(6270,6417),(6271,6418),(6272,6419),(6273,6420),(6274,6421),(6275,6422),(6276,6423),(6277,6424),(6278,6425),(6279,6426),(6280,6427),(6281,6428),(6282,6429),(6283,6430),(6284,6431),(6285,6432),(6286,6433),(6287,6434),(6288,6435),(6289,6436),(6290,6437),(6291,6438),(6292,6439),(6293,6440),(6294,6441),(6295,6442),(6296,6443),(6297,6444),(6298,6445),(6299,6446),(6300,6447),(6301,6448),(6302,6449),(6303,6450),(6304,6451),(6305,6452),(6306,6453),(6307,6454),(6308,6455),(6309,6456),(6310,6457),(6311,6458),(6312,6459),(6313,6460),(6314,6461),(6315,6462),(6316,6463),(6317,6464),(6318,6465),(6319,6466),(6320,6467),(6321,6468),(6322,6469),(6323,6470),(6324,6471),(6325,6472),(6326,6473),(6327,6474),(6328,6475),(6329,6476),(6330,6477),(6331,6478),(6332,6479),(6333,6480),(6334,6481),(6335,6482),(6336,6483),(6337,6484),(6338,6485),(6339,6486),(6340,6487),(6341,6488),(6342,6489),(6343,6490),(6344,6491),(6345,6492),(6346,6493),(6347,6494),(6348,6495),(6349,6496),(6350,6497),(6351,6498),(6352,6499),(6353,6500),(6354,6501),(6355,6502),(6356,6503),(6357,6504),(6358,6505),(6359,6506),(6360,6507),(6361,6508),(6362,6509),(6363,6510),(6364,6511),(6365,6512),(6366,6513),(6367,6514),(6368,6515),(6369,6516),(6370,6517),(6371,6518),(6372,6519),(6373,6520),(6374,6521),(6375,6522),(6376,6523),(6377,6524),(6378,6525),(6379,6526),(6380,6527),(6381,6528),(6382,6529),(6383,6530),(6384,6531),(6385,6532),(6386,6533),(6387,6534),(6388,6535),(6389,6536),(6390,6537),(6391,6538),(6392,6539),(6393,6540),(6394,6541),(6395,6542),(6396,6543),(6397,6544),(6398,6545),(6399,6546)]
theorem count : slots.length=254 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0024

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0024.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0024.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0024.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0024.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0024.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0024.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0024.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0024.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0024.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0024.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0024.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0024.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0024.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0024.sound
