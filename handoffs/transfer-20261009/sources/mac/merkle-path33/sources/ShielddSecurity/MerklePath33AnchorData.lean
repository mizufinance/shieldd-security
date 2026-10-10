import ShielddSecurity.MerkleFamily32Tables
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.MerklePath33AnchorData
open Compiler CompilerIndexed01
open CapturedInitial73419Generic01 (p copy)
def output : Linear := [(32222,5579934908212736977238010113730457006906792843192217773053283881663622591681),(32226,50978946942794420813356136484142315443152313428221265043903658432145007475423),(32230,51737743277955608982399432577620617083998176562860787771480331520415801857016),(32234,280754542936071555323583947036382301904172335755315562603417507239324752636),(32238,44773762128641970103070913747625047847186741019957383563700055475244115610384),(32242,28552781024861804928696238677004241170376447700649499575281496751792046985224)]
def anchor : Row := ⟨[(4,52435875175126190479447740508185965837690552500527637822603658699938581184512),(32222,5579934908212736977238010113730457006906792843192217773053283881663622591681),(32226,50978946942794420813356136484142315443152313428221265043903658432145007475423),(32230,51737743277955608982399432577620617083998176562860787771480331520415801857016),(32234,280754542936071555323583947036382301904172335755315562603417507239324752636),(32238,44773762128641970103070913747625047847186741019957383563700055475244115610384),(32242,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[]⟩
theorem output_exact : MerkleFamily32Tables.resultList[14]?.getD []=output := by decide +kernel
theorem anchor_checked : checkRow p [anchor] ⟨subtract output [(4,1)],[]⟩=true := by decide +kernel
theorem reverse_checked : checkOriginalCoverage p 0 #[anchor] #[⟨subtract output [(4,1)],[]⟩] #[0]=true := by decide +kernel
end ShielddSecurity.MerklePath33AnchorData

set_option pp.all true in
#check @ShielddSecurity.MerklePath33AnchorData.output
#print axioms ShielddSecurity.MerklePath33AnchorData.output
set_option pp.all true in
#check @ShielddSecurity.MerklePath33AnchorData.anchor
#print axioms ShielddSecurity.MerklePath33AnchorData.anchor
set_option pp.all true in
#check @ShielddSecurity.MerklePath33AnchorData.output_exact
#print axioms ShielddSecurity.MerklePath33AnchorData.output_exact
set_option pp.all true in
#check @ShielddSecurity.MerklePath33AnchorData.anchor_checked
#print axioms ShielddSecurity.MerklePath33AnchorData.anchor_checked
set_option pp.all true in
#check @ShielddSecurity.MerklePath33AnchorData.reverse_checked
#print axioms ShielddSecurity.MerklePath33AnchorData.reverse_checked
