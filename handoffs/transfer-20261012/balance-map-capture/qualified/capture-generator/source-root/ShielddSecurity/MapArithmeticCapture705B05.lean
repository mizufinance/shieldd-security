-- GENERATED from extraction.json. Do not hand edit.
import ShielddSecurity.MapArithmeticAdapter704
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapArithmeticCapture705B05
open MapArithmeticAdapter704
noncomputable def entry0 : Entry := ⟨1169194,false,[(190215,1)],[(21196,1)],[(190217,1)],[(190218,1)],167479,[⟨[(21196,52435875175126190479447740508185965837690552500527637822603658699938581184512),(190215,1)],[(190218,1)]⟩,⟨[(21196,1),(190215,1)],[(190217,4),(190218,1)]⟩]⟩
theorem checked0 : check entry0=true := by decide +kernel
noncomputable def entry1 : Entry := ⟨1169196,false,[(190203,1),(190204,1)],[(190205,19257038036680949359750312669786877991949435402254120286184196891950884077233),(200692,1)],[(190219,1)],[(190220,1)],167481,[⟨[(190203,1),(190204,1),(190205,33178837138445241119697427838399087845741117098273517536419461807987697107280),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(190220,1)]⟩,⟨[(190203,1),(190204,1),(190205,19257038036680949359750312669786877991949435402254120286184196891950884077233),(200692,1)],[(190219,4),(190220,1)]⟩]⟩
theorem checked1 : check entry1=true := by decide +kernel
noncomputable def entry2 : Entry := ⟨1169197,false,[(190219,1)],[(21196,1)],[(190221,1)],[(190222,1)],167483,[⟨[(21196,52435875175126190479447740508185965837690552500527637822603658699938581184512),(190219,1)],[(190222,1)]⟩,⟨[(21196,1),(190219,1)],[(190221,4),(190222,1)]⟩]⟩
theorem checked2 : check entry2=true := by decide +kernel
noncomputable def entry3 : Entry := ⟨1169198,true,[(190217,1)],[(190217,1)],[(190223,1)],[],167485,[⟨[(190217,1)],[(190223,1)]⟩]⟩
theorem checked3 : check entry3=true := by decide +kernel
noncomputable def entry4 : Entry := ⟨1169199,true,[(190221,1)],[(190221,1)],[(190224,1)],[],167486,[⟨[(190221,1)],[(190224,1)]⟩]⟩
theorem checked4 : check entry4=true := by decide +kernel
noncomputable def entry5 : Entry := ⟨1169200,false,[(190223,1)],[(190224,1)],[(190225,1)],[(190226,1)],167487,[⟨[(190223,1),(190224,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(190226,1)]⟩,⟨[(190223,1),(190224,1)],[(190225,4),(190226,1)]⟩]⟩
theorem checked5 : check entry5=true := by decide +kernel
noncomputable def entry6 : Entry := ⟨1169205,false,[(190225,19257038036680949359750312669786877991949435402254120286184196891950884077233),(200692,1)],[(190225,33178837138445241119697427838399087845741117098273517536419461807987697107280),(200692,1)],[(190227,1)],[(190228,1)],167489,[⟨[(190225,38514076073361898719500625339573755983898870804508240572368393783901768154466)],[(190228,1)]⟩,⟨[(200692,2)],[(190227,4),(190228,1)]⟩]⟩
theorem checked6 : check entry6=true := by decide +kernel
noncomputable def entries : List Entry := [entry0,entry1,entry2,entry3,entry4,entry5,entry6]
theorem checked : entries.all check=true := by
  simp only [entries,List.all_cons,List.all_nil,checked0,checked1,checked2,checked3,checked4,checked5,checked6,Bool.true_and]
end ShielddSecurity.MapArithmeticCapture705B05

set_option pp.all true in
#check @ShielddSecurity.MapArithmeticCapture705B05.checked
#print axioms ShielddSecurity.MapArithmeticCapture705B05.checked
