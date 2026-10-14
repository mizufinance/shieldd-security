import ShielddSecurity.BalanceMapSeed703
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapSeedValues724
open ConcreteJubjubField01

theorem initial (u : F) : BalanceMapSeed703.value u 20934=(BalanceMapParameters699.sourceDenominator u)⁻¹ := rfl

theorem qr (u : F) : BalanceMapSeed703.value u 20936=BalanceMapRoots700.qrRoot u := rfl

theorem selected (u : F) : BalanceMapSeed703.value u 20937=BalanceMapRoots700.selectedRoot u := rfl

theorem zero (u : F) : BalanceMapSeed703.value u 21193=BalanceMapPoint701.zero u := by
  unfold BalanceMapSeed703.value
  rw [if_neg (show ¬(21193=20934) by decide),if_neg (show ¬(21193=20935) by decide),
    if_neg (show ¬(21193=20936) by decide),if_neg (show ¬(21193=20937) by decide),if_pos rfl]

theorem inverse (u : F) : BalanceMapSeed703.value u 21194=(BalanceMapPoint701.denominator u)⁻¹ := rfl

theorem first (u : F) : BalanceMapSeed703.value u 21195=BalanceMapSeed703.addInverse (BalanceMapPoint701.preimage u) := rfl

theorem second (u : F) : BalanceMapSeed703.value u 21196=BalanceMapSeed703.addInverse (BalanceMapPoint701.twice u) := rfl

theorem third (u : F) : BalanceMapSeed703.value u 21197=BalanceMapSeed703.addInverse (BalanceMapPoint701.four u) := rfl

theorem last (u : F) : BalanceMapSeed703.value u 21198=(BalanceMapPoint701.eight u).x⁻¹ := rfl
end ShielddSecurity.MapSeedValues724

set_option pp.all true in
#check @ShielddSecurity.MapSeedValues724.initial
#print axioms ShielddSecurity.MapSeedValues724.initial

set_option pp.all true in
#check @ShielddSecurity.MapSeedValues724.qr
#print axioms ShielddSecurity.MapSeedValues724.qr

set_option pp.all true in
#check @ShielddSecurity.MapSeedValues724.selected
#print axioms ShielddSecurity.MapSeedValues724.selected

set_option pp.all true in
#check @ShielddSecurity.MapSeedValues724.zero
#print axioms ShielddSecurity.MapSeedValues724.zero

set_option pp.all true in
#check @ShielddSecurity.MapSeedValues724.inverse
#print axioms ShielddSecurity.MapSeedValues724.inverse

set_option pp.all true in
#check @ShielddSecurity.MapSeedValues724.first
#print axioms ShielddSecurity.MapSeedValues724.first

set_option pp.all true in
#check @ShielddSecurity.MapSeedValues724.second
#print axioms ShielddSecurity.MapSeedValues724.second

set_option pp.all true in
#check @ShielddSecurity.MapSeedValues724.third
#print axioms ShielddSecurity.MapSeedValues724.third

set_option pp.all true in
#check @ShielddSecurity.MapSeedValues724.last
#print axioms ShielddSecurity.MapSeedValues724.last
