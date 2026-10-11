import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0029
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(7461,7597),(7464,7599),(7467,7601),(7470,7603),(7473,7605),(7474,7606),(7476,7610),(7477,7611),(7478,7612),(7479,7613),(7480,7614),(7481,7615),(7482,7616),(7483,7617),(7484,7618),(7485,7619),(7486,7620),(7487,7621),(7488,7622),(7489,7623),(7490,7624),(7491,7625),(7492,7626),(7493,7627),(7494,7628),(7495,7629),(7496,7630),(7497,7631),(7498,7632),(7499,7633),(7500,7634),(7501,7635),(7502,7636),(7503,7637),(7504,7638),(7505,7639),(7506,7640),(7507,7641),(7508,7642),(7509,7643),(7510,7644),(7511,7645),(7512,7646),(7513,7647),(7514,7648),(7515,7649),(7516,7650),(7517,7651),(7518,7652),(7519,7653),(7520,7654),(7521,7655),(7522,7656),(7523,7657),(7524,7658),(7525,7659),(7526,7660),(7527,7661),(7528,7662),(7529,7663),(7530,7664),(7531,7665),(7532,7666),(7533,7667),(7534,7668),(7535,7669),(7536,7670),(7537,7671),(7538,7672),(7539,7673),(7541,7674),(7542,7675),(7543,7676),(7544,7677),(7545,7678),(7546,7679),(7547,7680),(7548,7681),(7549,7682),(7550,7683),(7551,7684),(7552,7685),(7553,7686),(7554,7687),(7555,7688),(7556,7689),(7557,7690),(7558,7691),(7559,7692),(7560,7693),(7561,7694),(7562,7695),(7563,7696),(7564,7697),(7565,7698),(7566,7699),(7567,7700),(7568,7701),(7569,7702),(7570,7703),(7571,7704),(7572,7705),(7573,7706),(7574,7707),(7575,7708),(7576,7709),(7577,7710),(7578,7711),(7579,7712),(7580,7713),(7581,7714),(7582,7715),(7583,7716),(7584,7717),(7585,7718),(7586,7719),(7587,7720),(7588,7721),(7590,7722),(7591,7723),(7592,7724),(7593,7725),(7594,7726),(7595,7727),(7596,7728),(7597,7729),(7598,7730),(7599,7731),(7600,7732),(7601,7733),(7602,7734),(7603,7735),(7604,7736),(7605,7737),(7606,7738),(7614,7743),(7615,7744),(7616,7745),(7617,7746),(7618,7747),(7619,7748),(7620,7749),(7621,7750),(7622,7751),(7623,7752),(7624,7753),(7625,7754),(7626,7755),(7627,7756),(7628,7757),(7629,7758),(7630,7759),(7631,7760),(7632,7761),(7633,7762),(7634,7763),(7635,7764),(7636,7765),(7637,7766),(7638,7767),(7639,7768),(7640,7769),(7641,7770),(7642,7771),(7643,7772),(7644,7773),(7645,7774),(7646,7775),(7647,7776),(7648,7777),(7649,7778),(7650,7779),(7651,7780),(7652,7781),(7653,7782),(7654,7783),(7655,7784),(7656,7785),(7657,7786),(7658,7787),(7659,7788),(7660,7789),(7661,7790),(7662,7791),(7663,7792),(7664,7793),(7665,7794),(7666,7795),(7667,7796),(7668,7797),(7669,7798),(7670,7799),(7671,7800),(7672,7801),(7673,7802),(7674,7803),(7675,7804),(7676,7805),(7677,7806),(7678,7807),(7679,7808)]
theorem count : slots.length=201 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0029

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0029.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0029.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0029.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0029.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0029.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0029.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0029.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0029.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0029.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0029.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0029.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0029.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0029.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0029.sound
