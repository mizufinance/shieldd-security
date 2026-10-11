import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0030
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(7680,7809),(7681,7810),(7682,7811),(7683,7812),(7684,7813),(7685,7814),(7686,7815),(7687,7816),(7688,7817),(7689,7818),(7690,7819),(7691,7820),(7692,7821),(7693,7822),(7694,7823),(7695,7824),(7696,7825),(7697,7826),(7698,7827),(7699,7828),(7700,7829),(7701,7830),(7702,7831),(7703,7832),(7704,7833),(7705,7834),(7706,7835),(7707,7836),(7708,7837),(7709,7838),(7710,7839),(7711,7840),(7712,7841),(7713,7842),(7714,7843),(7715,7844),(7716,7845),(7717,7846),(7718,7847),(7719,7848),(7720,7849),(7721,7850),(7722,7851),(7723,7852),(7724,7853),(7725,7854),(7726,7855),(7727,7856),(7728,7857),(7729,7858),(7730,7859),(7731,7860),(7732,7861),(7733,7862),(7734,7863),(7735,7864),(7736,7865),(7737,7866),(7738,7867),(7739,7868),(7740,7869),(7741,7870),(7743,7871),(7744,7872),(7745,7873),(7746,7874),(7747,7875),(7748,7876),(7749,7877),(7750,7878),(7751,7879),(7752,7880),(7753,7881),(7754,7882),(7755,7883),(7756,7884),(7757,7885),(7758,7886),(7759,7887),(7760,7888),(7761,7889),(7762,7890),(7763,7891),(7764,7892),(7765,7893),(7766,7894),(7767,7895),(7768,7896),(7769,7897),(7770,7898),(7771,7899),(7772,7900),(7773,7901),(7774,7902),(7775,7903),(7776,7904),(7777,7905),(7778,7906),(7779,7907),(7780,7908),(7781,7909),(7782,7910),(7783,7911),(7784,7912),(7785,7913),(7786,7914),(7787,7915),(7788,7916),(7789,7917),(7790,7918),(7791,7919),(7792,7920),(7793,7921),(7794,7922),(7795,7923),(7796,7924),(7797,7925),(7798,7926),(7799,7927),(7800,7928),(7801,7929),(7802,7930),(7803,7931),(7804,7932),(7805,7933),(7806,7934),(7807,7935),(7808,7936),(7809,7937),(7810,7938),(7811,7939),(7812,7940),(7813,7941),(7814,7942),(7815,7943),(7816,7944),(7817,7945),(7818,7946),(7819,7947),(7820,7948),(7821,7949),(7822,7950),(7823,7951),(7824,7952),(7825,7953),(7826,7954),(7827,7955),(7828,7956),(7829,7957),(7830,7958),(7831,7959),(7832,7960),(7833,7961),(7834,7962),(7835,7963),(7836,7964),(7837,7965),(7838,7966),(7839,7967),(7840,7968),(7841,7969),(7842,7970),(7843,7971),(7844,7972),(7845,7973),(7846,7974),(7847,7975),(7848,7976),(7849,7977),(7850,7978),(7851,7979),(7852,7980),(7853,7981),(7854,7982),(7855,7983),(7856,7984),(7857,7985),(7858,7986),(7859,7987),(7860,7988),(7861,7989),(7862,7990),(7863,7991),(7864,7992),(7865,7993),(7866,7994),(7867,7995),(7868,7996),(7869,7997),(7870,7998),(7872,7999),(7873,8000),(7874,8001),(7875,8002),(7876,8003),(7877,8004),(7878,8005),(7879,8006),(7880,8007),(7881,8008),(7882,8009),(7883,8010),(7884,8011),(7885,8012),(7886,8013),(7887,8014),(7888,8015),(7889,8016),(7890,8017),(7891,8018),(7892,8019),(7893,8020),(7894,8021),(7895,8022),(7896,8023),(7897,8024),(7898,8025),(7899,8026),(7900,8027),(7901,8028),(7902,8029),(7903,8030),(7904,8031),(7905,8032),(7906,8033),(7907,8034),(7908,8035),(7909,8036),(7910,8037),(7911,8038),(7912,8039),(7913,8040),(7914,8041),(7915,8042),(7916,8043),(7917,8044),(7918,8045),(7919,8046),(7920,8047),(7921,8048),(7922,8049),(7923,8050),(7924,8051),(7925,8052),(7926,8053),(7927,8054),(7928,8055),(7929,8056),(7930,8057),(7931,8058),(7932,8059),(7933,8060),(7934,8061),(7935,8062)]
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
end ShielddSecurity.CapturedBooleanSlots208B0030

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0030.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0030.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0030.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0030.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0030.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0030.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0030.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0030.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0030.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0030.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0030.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0030.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0030.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0030.sound
