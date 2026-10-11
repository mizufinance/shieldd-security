import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0001
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(256,307),(257,308),(258,309),(259,310),(260,311),(261,312),(262,313),(263,314),(264,315),(265,316),(266,317),(267,318),(268,319),(269,320),(270,321),(271,322),(272,323),(273,324),(274,325),(275,326),(276,327),(277,328),(278,329),(279,330),(280,331),(281,332),(282,333),(283,334),(284,335),(285,336),(286,337),(287,338),(288,339),(289,340),(290,341),(291,342),(292,343),(293,344),(294,345),(295,346),(296,347),(297,348),(298,349),(299,350),(300,351),(301,352),(302,353),(303,354),(304,355),(305,356),(306,357),(307,358),(308,359),(309,360),(310,361),(311,362),(312,363),(313,364),(314,365),(315,366),(316,367),(317,368),(318,369),(319,370),(320,371),(321,372),(322,373),(323,374),(324,375),(325,376),(326,377),(327,378),(328,379),(329,380),(330,381),(331,382),(332,383),(333,384),(334,385),(335,386),(336,387),(337,388),(338,389),(339,390),(340,391),(341,392),(342,393),(343,394),(344,395),(345,396),(346,397),(347,398),(348,399),(349,400),(350,401),(351,402),(352,403),(353,404),(354,405),(355,406),(356,407),(357,408),(358,409),(359,410),(360,411),(361,412),(362,413),(363,414),(364,415),(365,416),(366,417),(367,418),(368,419),(369,420),(370,421),(371,422),(372,423),(373,424),(374,425),(375,426),(376,427),(377,428),(378,429),(379,430),(380,431),(381,432),(382,433),(383,434),(384,435),(385,436),(386,437),(387,438),(388,439),(389,440),(390,441),(391,442),(392,443),(393,444),(394,445),(395,446),(396,447),(397,448),(398,449),(399,450),(400,451),(401,452),(402,453),(403,454),(404,455),(405,456),(406,457),(407,458),(408,459),(409,460),(410,461),(411,462),(412,463),(413,464),(414,465),(415,466),(416,467),(417,468),(418,469),(419,470),(423,471),(424,472),(425,473),(426,474),(427,475),(428,476),(429,477),(430,478),(431,479),(432,480),(433,481),(434,482),(435,483),(436,484),(437,485),(438,486),(439,487),(440,488),(441,489),(442,490),(443,491),(444,492),(445,493),(446,494),(447,495),(448,496),(449,497),(450,498),(451,499),(452,500),(453,501),(454,502),(455,503),(456,504),(457,505),(458,506),(459,507),(460,508),(461,509),(462,510),(463,511),(464,512),(465,513),(466,514),(467,515),(468,516),(469,517),(470,518),(471,519),(472,520),(473,521),(474,522),(475,523),(476,524),(477,525),(478,526),(479,527),(480,528),(481,529),(482,530),(483,531),(484,532),(485,533),(486,534),(487,535),(488,536),(489,537),(490,538),(491,539),(492,540),(493,541),(494,542),(495,543),(496,544),(497,545),(498,546),(499,547),(500,548),(501,549),(502,550),(503,551),(504,552),(505,553),(506,554),(507,555),(508,556),(509,557),(510,558),(511,559)]
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
end ShielddSecurity.CapturedBooleanSlots208B0001

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0001.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0001.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0001.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0001.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0001.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0001.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0001.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0001.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0001.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0001.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0001.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0001.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0001.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0001.sound
